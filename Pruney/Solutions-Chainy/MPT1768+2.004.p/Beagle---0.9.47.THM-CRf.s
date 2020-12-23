%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:17 EST 2020

% Result     : Theorem 9.51s
% Output     : CNFRefutation 9.51s
% Verified   : 
% Statistics : Number of formulae       :  170 (4775 expanded)
%              Number of leaves         :   33 (1876 expanded)
%              Depth                    :   35
%              Number of atoms          :  723 (38744 expanded)
%              Number of equality atoms :   47 ( 856 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_270,negated_conjecture,(
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
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(D,C)
                            & m1_pre_topc(E,D) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_223,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

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

tff(f_130,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_164,axiom,(
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
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_211,axiom,(
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
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_32,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_60,plain,(
    ! [B_202,A_203] :
      ( l1_pre_topc(B_202)
      | ~ m1_pre_topc(B_202,A_203)
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_82,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_66])).

tff(c_16,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_95,plain,(
    ! [B_204,A_205] :
      ( v2_pre_topc(B_204)
      | ~ m1_pre_topc(B_204,A_205)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_95])).

tff(c_117,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_101])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_104,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_95])).

tff(c_120,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_104])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_60])).

tff(c_85,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_130,plain,(
    ! [C_206,A_207,B_208] :
      ( m1_pre_topc(C_206,A_207)
      | ~ m1_pre_topc(C_206,B_208)
      | ~ m1_pre_topc(B_208,A_207)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_175,plain,(
    ! [A_211] :
      ( m1_pre_topc('#skF_5',A_211)
      | ~ m1_pre_topc('#skF_4',A_211)
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211) ) ),
    inference(resolution,[status(thm)],[c_32,c_130])).

tff(c_22,plain,(
    ! [C_143,A_137,B_141] :
      ( m1_pre_topc(C_143,A_137)
      | ~ m1_pre_topc(C_143,B_141)
      | ~ m1_pre_topc(B_141,A_137)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_335,plain,(
    ! [A_230,A_231] :
      ( m1_pre_topc('#skF_5',A_230)
      | ~ m1_pre_topc(A_231,A_230)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | ~ m1_pre_topc('#skF_4',A_231)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231) ) ),
    inference(resolution,[status(thm)],[c_175,c_22])).

tff(c_349,plain,
    ( m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_335])).

tff(c_372,plain,
    ( m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_82,c_120,c_85,c_349])).

tff(c_379,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_382,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_379])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_382])).

tff(c_387,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_28,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_566,plain,(
    ! [E_255,C_256,B_254,A_253,D_252] :
      ( k3_tmap_1(A_253,B_254,C_256,D_252,E_255) = k2_partfun1(u1_struct_0(C_256),u1_struct_0(B_254),E_255,u1_struct_0(D_252))
      | ~ m1_pre_topc(D_252,C_256)
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_256),u1_struct_0(B_254))))
      | ~ v1_funct_2(E_255,u1_struct_0(C_256),u1_struct_0(B_254))
      | ~ v1_funct_1(E_255)
      | ~ m1_pre_topc(D_252,A_253)
      | ~ m1_pre_topc(C_256,A_253)
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_570,plain,(
    ! [A_253,D_252] :
      ( k3_tmap_1(A_253,'#skF_2','#skF_3',D_252,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_252))
      | ~ m1_pre_topc(D_252,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_252,A_253)
      | ~ m1_pre_topc('#skF_3',A_253)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_26,c_566])).

tff(c_574,plain,(
    ! [A_253,D_252] :
      ( k3_tmap_1(A_253,'#skF_2','#skF_3',D_252,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_252))
      | ~ m1_pre_topc(D_252,'#skF_3')
      | ~ m1_pre_topc(D_252,A_253)
      | ~ m1_pre_topc('#skF_3',A_253)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_28,c_570])).

tff(c_576,plain,(
    ! [A_257,D_258] :
      ( k3_tmap_1(A_257,'#skF_2','#skF_3',D_258,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_258))
      | ~ m1_pre_topc(D_258,'#skF_3')
      | ~ m1_pre_topc(D_258,A_257)
      | ~ m1_pre_topc('#skF_3',A_257)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_574])).

tff(c_592,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_576])).

tff(c_622,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_34,c_592])).

tff(c_623,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_622])).

tff(c_319,plain,(
    ! [A_225,B_226,C_227,D_228] :
      ( k2_partfun1(u1_struct_0(A_225),u1_struct_0(B_226),C_227,u1_struct_0(D_228)) = k2_tmap_1(A_225,B_226,C_227,D_228)
      | ~ m1_pre_topc(D_228,A_225)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225),u1_struct_0(B_226))))
      | ~ v1_funct_2(C_227,u1_struct_0(A_225),u1_struct_0(B_226))
      | ~ v1_funct_1(C_227)
      | ~ l1_pre_topc(B_226)
      | ~ v2_pre_topc(B_226)
      | v2_struct_0(B_226)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_321,plain,(
    ! [D_228] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_228)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_228)
      | ~ m1_pre_topc(D_228,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_319])).

tff(c_324,plain,(
    ! [D_228] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_228)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_228)
      | ~ m1_pre_topc(D_228,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_85,c_50,c_48,c_30,c_28,c_321])).

tff(c_325,plain,(
    ! [D_228] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_228)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_228)
      | ~ m1_pre_topc(D_228,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_52,c_324])).

tff(c_643,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_325])).

tff(c_650,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_643])).

tff(c_189,plain,(
    ! [A_213,D_215,B_216,C_212,E_214] :
      ( v1_funct_1(k3_tmap_1(A_213,B_216,C_212,D_215,E_214))
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212),u1_struct_0(B_216))))
      | ~ v1_funct_2(E_214,u1_struct_0(C_212),u1_struct_0(B_216))
      | ~ v1_funct_1(E_214)
      | ~ m1_pre_topc(D_215,A_213)
      | ~ m1_pre_topc(C_212,A_213)
      | ~ l1_pre_topc(B_216)
      | ~ v2_pre_topc(B_216)
      | v2_struct_0(B_216)
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_191,plain,(
    ! [A_213,D_215] :
      ( v1_funct_1(k3_tmap_1(A_213,'#skF_2','#skF_3',D_215,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_215,A_213)
      | ~ m1_pre_topc('#skF_3',A_213)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(resolution,[status(thm)],[c_26,c_189])).

tff(c_194,plain,(
    ! [A_213,D_215] :
      ( v1_funct_1(k3_tmap_1(A_213,'#skF_2','#skF_3',D_215,'#skF_6'))
      | ~ m1_pre_topc(D_215,A_213)
      | ~ m1_pre_topc('#skF_3',A_213)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_28,c_191])).

tff(c_195,plain,(
    ! [A_213,D_215] :
      ( v1_funct_1(k3_tmap_1(A_213,'#skF_2','#skF_3',D_215,'#skF_6'))
      | ~ m1_pre_topc(D_215,A_213)
      | ~ m1_pre_topc('#skF_3',A_213)
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_194])).

tff(c_665,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_195])).

tff(c_675,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_40,c_665])).

tff(c_676,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_675])).

tff(c_537,plain,(
    ! [D_238,C_235,B_239,E_237,A_236] :
      ( v1_funct_2(k3_tmap_1(A_236,B_239,C_235,D_238,E_237),u1_struct_0(D_238),u1_struct_0(B_239))
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_235),u1_struct_0(B_239))))
      | ~ v1_funct_2(E_237,u1_struct_0(C_235),u1_struct_0(B_239))
      | ~ v1_funct_1(E_237)
      | ~ m1_pre_topc(D_238,A_236)
      | ~ m1_pre_topc(C_235,A_236)
      | ~ l1_pre_topc(B_239)
      | ~ v2_pre_topc(B_239)
      | v2_struct_0(B_239)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_539,plain,(
    ! [A_236,D_238] :
      ( v1_funct_2(k3_tmap_1(A_236,'#skF_2','#skF_3',D_238,'#skF_6'),u1_struct_0(D_238),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_238,A_236)
      | ~ m1_pre_topc('#skF_3',A_236)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_26,c_537])).

tff(c_542,plain,(
    ! [A_236,D_238] :
      ( v1_funct_2(k3_tmap_1(A_236,'#skF_2','#skF_3',D_238,'#skF_6'),u1_struct_0(D_238),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_238,A_236)
      | ~ m1_pre_topc('#skF_3',A_236)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_28,c_539])).

tff(c_543,plain,(
    ! [A_236,D_238] :
      ( v1_funct_2(k3_tmap_1(A_236,'#skF_2','#skF_3',D_238,'#skF_6'),u1_struct_0(D_238),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_238,A_236)
      | ~ m1_pre_topc('#skF_3',A_236)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_542])).

tff(c_662,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_543])).

tff(c_672,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_40,c_662])).

tff(c_673,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_672])).

tff(c_10,plain,(
    ! [A_53,D_56,E_57,C_55,B_54] :
      ( m1_subset_1(k3_tmap_1(A_53,B_54,C_55,D_56,E_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_56),u1_struct_0(B_54))))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_55),u1_struct_0(B_54))))
      | ~ v1_funct_2(E_57,u1_struct_0(C_55),u1_struct_0(B_54))
      | ~ v1_funct_1(E_57)
      | ~ m1_pre_topc(D_56,A_53)
      | ~ m1_pre_topc(C_55,A_53)
      | ~ l1_pre_topc(B_54)
      | ~ v2_pre_topc(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_659,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_10])).

tff(c_669,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_44,c_40,c_30,c_28,c_26,c_659])).

tff(c_670,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_669])).

tff(c_6,plain,(
    ! [A_7,B_15,C_19,D_21] :
      ( k2_partfun1(u1_struct_0(A_7),u1_struct_0(B_15),C_19,u1_struct_0(D_21)) = k2_tmap_1(A_7,B_15,C_19,D_21)
      | ~ m1_pre_topc(D_21,A_7)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7),u1_struct_0(B_15))))
      | ~ v1_funct_2(C_19,u1_struct_0(A_7),u1_struct_0(B_15))
      | ~ v1_funct_1(C_19)
      | ~ l1_pre_topc(B_15)
      | ~ v2_pre_topc(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_687,plain,(
    ! [D_21] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_21)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_21)
      | ~ m1_pre_topc(D_21,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_670,c_6])).

tff(c_704,plain,(
    ! [D_21] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_21)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_21)
      | ~ m1_pre_topc(D_21,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_82,c_50,c_48,c_676,c_673,c_687])).

tff(c_705,plain,(
    ! [D_21] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_21)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_21)
      | ~ m1_pre_topc(D_21,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_52,c_704])).

tff(c_594,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_576])).

tff(c_626,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_594])).

tff(c_627,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_626])).

tff(c_829,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_627])).

tff(c_835,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_829])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_835])).

tff(c_844,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_654,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_623])).

tff(c_596,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_576])).

tff(c_630,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_85,c_34,c_596])).

tff(c_631,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_630])).

tff(c_827,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_631])).

tff(c_828,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_827])).

tff(c_893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_828])).

tff(c_895,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_894,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_1369,plain,(
    ! [D_303,E_302,B_306,D_304,C_300,A_301,A_305] :
      ( k3_tmap_1(A_305,B_306,D_304,D_303,k3_tmap_1(A_301,B_306,C_300,D_304,E_302)) = k2_partfun1(u1_struct_0(D_304),u1_struct_0(B_306),k3_tmap_1(A_301,B_306,C_300,D_304,E_302),u1_struct_0(D_303))
      | ~ m1_pre_topc(D_303,D_304)
      | ~ v1_funct_2(k3_tmap_1(A_301,B_306,C_300,D_304,E_302),u1_struct_0(D_304),u1_struct_0(B_306))
      | ~ v1_funct_1(k3_tmap_1(A_301,B_306,C_300,D_304,E_302))
      | ~ m1_pre_topc(D_303,A_305)
      | ~ m1_pre_topc(D_304,A_305)
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_300),u1_struct_0(B_306))))
      | ~ v1_funct_2(E_302,u1_struct_0(C_300),u1_struct_0(B_306))
      | ~ v1_funct_1(E_302)
      | ~ m1_pre_topc(D_304,A_301)
      | ~ m1_pre_topc(C_300,A_301)
      | ~ l1_pre_topc(B_306)
      | ~ v2_pre_topc(B_306)
      | v2_struct_0(B_306)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_10,c_566])).

tff(c_1379,plain,(
    ! [A_305,D_304,D_303,A_301] :
      ( k3_tmap_1(A_305,'#skF_2',D_304,D_303,k3_tmap_1(A_301,'#skF_2','#skF_3',D_304,'#skF_6')) = k2_partfun1(u1_struct_0(D_304),u1_struct_0('#skF_2'),k3_tmap_1(A_301,'#skF_2','#skF_3',D_304,'#skF_6'),u1_struct_0(D_303))
      | ~ m1_pre_topc(D_303,D_304)
      | ~ v1_funct_2(k3_tmap_1(A_301,'#skF_2','#skF_3',D_304,'#skF_6'),u1_struct_0(D_304),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_301,'#skF_2','#skF_3',D_304,'#skF_6'))
      | ~ m1_pre_topc(D_303,A_305)
      | ~ m1_pre_topc(D_304,A_305)
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_304,A_301)
      | ~ m1_pre_topc('#skF_3',A_301)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_26,c_1369])).

tff(c_1395,plain,(
    ! [A_305,D_304,D_303,A_301] :
      ( k3_tmap_1(A_305,'#skF_2',D_304,D_303,k3_tmap_1(A_301,'#skF_2','#skF_3',D_304,'#skF_6')) = k2_partfun1(u1_struct_0(D_304),u1_struct_0('#skF_2'),k3_tmap_1(A_301,'#skF_2','#skF_3',D_304,'#skF_6'),u1_struct_0(D_303))
      | ~ m1_pre_topc(D_303,D_304)
      | ~ v1_funct_2(k3_tmap_1(A_301,'#skF_2','#skF_3',D_304,'#skF_6'),u1_struct_0(D_304),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_301,'#skF_2','#skF_3',D_304,'#skF_6'))
      | ~ m1_pre_topc(D_303,A_305)
      | ~ m1_pre_topc(D_304,A_305)
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305)
      | ~ m1_pre_topc(D_304,A_301)
      | ~ m1_pre_topc('#skF_3',A_301)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_28,c_1379])).

tff(c_1752,plain,(
    ! [A_333,D_334,D_335,A_336] :
      ( k3_tmap_1(A_333,'#skF_2',D_334,D_335,k3_tmap_1(A_336,'#skF_2','#skF_3',D_334,'#skF_6')) = k2_partfun1(u1_struct_0(D_334),u1_struct_0('#skF_2'),k3_tmap_1(A_336,'#skF_2','#skF_3',D_334,'#skF_6'),u1_struct_0(D_335))
      | ~ m1_pre_topc(D_335,D_334)
      | ~ v1_funct_2(k3_tmap_1(A_336,'#skF_2','#skF_3',D_334,'#skF_6'),u1_struct_0(D_334),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_336,'#skF_2','#skF_3',D_334,'#skF_6'))
      | ~ m1_pre_topc(D_335,A_333)
      | ~ m1_pre_topc(D_334,A_333)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333)
      | ~ m1_pre_topc(D_334,A_336)
      | ~ m1_pre_topc('#skF_3',A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1395])).

tff(c_1821,plain,(
    ! [A_333,D_335] :
      ( k3_tmap_1(A_333,'#skF_2','#skF_4',D_335,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_4','#skF_6'),u1_struct_0(D_335))
      | ~ m1_pre_topc(D_335,'#skF_4')
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_4','#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(D_335,A_333)
      | ~ m1_pre_topc('#skF_4',A_333)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333)
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_894,c_1752])).

tff(c_1879,plain,(
    ! [A_333,D_335] :
      ( k3_tmap_1(A_333,'#skF_2','#skF_4',D_335,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_335))
      | ~ m1_pre_topc(D_335,'#skF_4')
      | ~ m1_pre_topc(D_335,A_333)
      | ~ m1_pre_topc('#skF_4',A_333)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_85,c_895,c_34,c_676,c_894,c_673,c_894,c_894,c_1821])).

tff(c_2155,plain,(
    ! [A_353,D_354] :
      ( k3_tmap_1(A_353,'#skF_2','#skF_4',D_354,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_354))
      | ~ m1_pre_topc(D_354,'#skF_4')
      | ~ m1_pre_topc(D_354,A_353)
      | ~ m1_pre_topc('#skF_4',A_353)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1879])).

tff(c_4371,plain,(
    ! [A_411,D_412] :
      ( k3_tmap_1(A_411,'#skF_2','#skF_4',D_412,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_412)
      | ~ m1_pre_topc(D_412,'#skF_4')
      | ~ m1_pre_topc(D_412,A_411)
      | ~ m1_pre_topc('#skF_4',A_411)
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411)
      | ~ m1_pre_topc(D_412,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_2155])).

tff(c_575,plain,(
    ! [A_253,D_252] :
      ( k3_tmap_1(A_253,'#skF_2','#skF_3',D_252,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_252))
      | ~ m1_pre_topc(D_252,'#skF_3')
      | ~ m1_pre_topc(D_252,A_253)
      | ~ m1_pre_topc('#skF_3',A_253)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_574])).

tff(c_897,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_895,c_575])).

tff(c_919,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_85,c_895,c_897])).

tff(c_920,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_919])).

tff(c_995,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_325])).

tff(c_1002,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_995])).

tff(c_545,plain,(
    ! [C_242,B_243,D_244,A_245] :
      ( r2_funct_2(u1_struct_0(C_242),u1_struct_0(B_243),D_244,k3_tmap_1(A_245,B_243,C_242,C_242,D_244))
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_242),u1_struct_0(B_243))))
      | ~ v1_funct_2(D_244,u1_struct_0(C_242),u1_struct_0(B_243))
      | ~ v1_funct_1(D_244)
      | ~ m1_pre_topc(C_242,A_245)
      | v2_struct_0(C_242)
      | ~ l1_pre_topc(B_243)
      | ~ v2_pre_topc(B_243)
      | v2_struct_0(B_243)
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_547,plain,(
    ! [A_245] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k3_tmap_1(A_245,'#skF_2','#skF_3','#skF_3','#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_3',A_245)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(resolution,[status(thm)],[c_26,c_545])).

tff(c_550,plain,(
    ! [A_245] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k3_tmap_1(A_245,'#skF_2','#skF_3','#skF_3','#skF_6'))
      | ~ m1_pre_topc('#skF_3',A_245)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_28,c_547])).

tff(c_551,plain,(
    ! [A_245] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k3_tmap_1(A_245,'#skF_2','#skF_3','#skF_3','#skF_6'))
      | ~ m1_pre_topc('#skF_3',A_245)
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_550])).

tff(c_1018,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_551])).

tff(c_1037,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_85,c_895,c_1018])).

tff(c_1038,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1037])).

tff(c_20,plain,(
    ! [A_74,D_130,C_122,E_134,F_136,B_106] :
      ( r2_funct_2(u1_struct_0(D_130),u1_struct_0(B_106),k3_tmap_1(A_74,B_106,C_122,D_130,F_136),k2_tmap_1(A_74,B_106,E_134,D_130))
      | ~ m1_pre_topc(D_130,C_122)
      | ~ r2_funct_2(u1_struct_0(C_122),u1_struct_0(B_106),F_136,k2_tmap_1(A_74,B_106,E_134,C_122))
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_122),u1_struct_0(B_106))))
      | ~ v1_funct_2(F_136,u1_struct_0(C_122),u1_struct_0(B_106))
      | ~ v1_funct_1(F_136)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74),u1_struct_0(B_106))))
      | ~ v1_funct_2(E_134,u1_struct_0(A_74),u1_struct_0(B_106))
      | ~ v1_funct_1(E_134)
      | ~ m1_pre_topc(D_130,A_74)
      | v2_struct_0(D_130)
      | ~ m1_pre_topc(C_122,A_74)
      | v2_struct_0(C_122)
      | ~ l1_pre_topc(B_106)
      | ~ v2_pre_topc(B_106)
      | v2_struct_0(B_106)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_1048,plain,(
    ! [D_130] :
      ( r2_funct_2(u1_struct_0(D_130),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_3',D_130,'#skF_6'),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_130))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_130,'#skF_3')
      | v2_struct_0(D_130)
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1038,c_20])).

tff(c_1051,plain,(
    ! [D_130] :
      ( r2_funct_2(u1_struct_0(D_130),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_3',D_130,'#skF_6'),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_130))
      | ~ m1_pre_topc(D_130,'#skF_3')
      | v2_struct_0(D_130)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_85,c_50,c_48,c_895,c_30,c_28,c_26,c_1048])).

tff(c_1213,plain,(
    ! [D_285] :
      ( r2_funct_2(u1_struct_0(D_285),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_3',D_285,'#skF_6'),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_285))
      | ~ m1_pre_topc(D_285,'#skF_3')
      | v2_struct_0(D_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_52,c_1051])).

tff(c_1224,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_894,c_1213])).

tff(c_1236,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1224])).

tff(c_1237,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1236])).

tff(c_1251,plain,(
    ! [D_130] :
      ( r2_funct_2(u1_struct_0(D_130),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_4',D_130,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_130))
      | ~ m1_pre_topc(D_130,'#skF_4')
      | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_130,'#skF_3')
      | v2_struct_0(D_130)
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1237,c_20])).

tff(c_1254,plain,(
    ! [D_130] :
      ( r2_funct_2(u1_struct_0(D_130),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_4',D_130,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_130))
      | ~ m1_pre_topc(D_130,'#skF_4')
      | ~ m1_pre_topc(D_130,'#skF_3')
      | v2_struct_0(D_130)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_85,c_50,c_48,c_34,c_30,c_28,c_26,c_676,c_673,c_670,c_1251])).

tff(c_1255,plain,(
    ! [D_130] :
      ( r2_funct_2(u1_struct_0(D_130),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_4',D_130,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_130))
      | ~ m1_pre_topc(D_130,'#skF_4')
      | ~ m1_pre_topc(D_130,'#skF_3')
      | v2_struct_0(D_130) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_52,c_42,c_1254])).

tff(c_4408,plain,(
    ! [D_412] :
      ( r2_funct_2(u1_struct_0(D_412),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_412),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_412))
      | ~ m1_pre_topc(D_412,'#skF_4')
      | ~ m1_pre_topc(D_412,'#skF_3')
      | v2_struct_0(D_412)
      | ~ m1_pre_topc(D_412,'#skF_4')
      | ~ m1_pre_topc(D_412,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_412,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4371,c_1255])).

tff(c_4461,plain,(
    ! [D_412] :
      ( r2_funct_2(u1_struct_0(D_412),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_412),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_412))
      | v2_struct_0(D_412)
      | ~ m1_pre_topc(D_412,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_412,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_85,c_34,c_4408])).

tff(c_4482,plain,(
    ! [D_413] :
      ( r2_funct_2(u1_struct_0(D_413),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_413),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_413))
      | v2_struct_0(D_413)
      | ~ m1_pre_topc(D_413,'#skF_3')
      | ~ m1_pre_topc(D_413,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4461])).

tff(c_36,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_598,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_576])).

tff(c_634,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_387,c_598])).

tff(c_635,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_634])).

tff(c_713,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_325])).

tff(c_720,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_713])).

tff(c_24,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_655,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_24])).

tff(c_1212,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_655])).

tff(c_4423,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4371,c_1212])).

tff(c_4470,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56,c_54,c_40,c_36,c_32,c_4423])).

tff(c_4471,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4470])).

tff(c_4485,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4482,c_4471])).

tff(c_4490,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_387,c_4485])).

tff(c_4492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:25:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.51/3.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.51/3.06  
% 9.51/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.51/3.06  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.51/3.06  
% 9.51/3.06  %Foreground sorts:
% 9.51/3.06  
% 9.51/3.06  
% 9.51/3.06  %Background operators:
% 9.51/3.06  
% 9.51/3.06  
% 9.51/3.06  %Foreground operators:
% 9.51/3.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.51/3.06  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 9.51/3.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.51/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.51/3.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.51/3.06  tff('#skF_5', type, '#skF_5': $i).
% 9.51/3.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.51/3.06  tff('#skF_6', type, '#skF_6': $i).
% 9.51/3.06  tff('#skF_2', type, '#skF_2': $i).
% 9.51/3.06  tff('#skF_3', type, '#skF_3': $i).
% 9.51/3.06  tff('#skF_1', type, '#skF_1': $i).
% 9.51/3.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.51/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.51/3.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.51/3.06  tff('#skF_4', type, '#skF_4': $i).
% 9.51/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.51/3.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.51/3.06  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.51/3.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.51/3.06  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 9.51/3.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.51/3.06  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 9.51/3.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.51/3.06  
% 9.51/3.09  tff(f_270, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(D, C) & m1_pre_topc(E, D)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(E), u1_struct_0(B), k3_tmap_1(A, B, D, E, k3_tmap_1(A, B, C, D, F)), k3_tmap_1(A, B, C, E, F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tmap_1)).
% 9.51/3.09  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.51/3.09  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.51/3.09  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 9.51/3.09  tff(f_223, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 9.51/3.09  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 9.51/3.09  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.51/3.09  tff(f_130, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 9.51/3.09  tff(f_164, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 9.51/3.09  tff(f_211, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 9.51/3.09  tff(c_38, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_32, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_60, plain, (![B_202, A_203]: (l1_pre_topc(B_202) | ~m1_pre_topc(B_202, A_203) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.51/3.09  tff(c_66, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_60])).
% 9.51/3.09  tff(c_82, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_66])).
% 9.51/3.09  tff(c_16, plain, (![A_58]: (m1_pre_topc(A_58, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.51/3.09  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_95, plain, (![B_204, A_205]: (v2_pre_topc(B_204) | ~m1_pre_topc(B_204, A_205) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.51/3.09  tff(c_101, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_95])).
% 9.51/3.09  tff(c_117, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_101])).
% 9.51/3.09  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_104, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_95])).
% 9.51/3.09  tff(c_120, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_104])).
% 9.51/3.09  tff(c_69, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_60])).
% 9.51/3.09  tff(c_85, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69])).
% 9.51/3.09  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_130, plain, (![C_206, A_207, B_208]: (m1_pre_topc(C_206, A_207) | ~m1_pre_topc(C_206, B_208) | ~m1_pre_topc(B_208, A_207) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.51/3.09  tff(c_175, plain, (![A_211]: (m1_pre_topc('#skF_5', A_211) | ~m1_pre_topc('#skF_4', A_211) | ~l1_pre_topc(A_211) | ~v2_pre_topc(A_211))), inference(resolution, [status(thm)], [c_32, c_130])).
% 9.51/3.09  tff(c_22, plain, (![C_143, A_137, B_141]: (m1_pre_topc(C_143, A_137) | ~m1_pre_topc(C_143, B_141) | ~m1_pre_topc(B_141, A_137) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.51/3.09  tff(c_335, plain, (![A_230, A_231]: (m1_pre_topc('#skF_5', A_230) | ~m1_pre_topc(A_231, A_230) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | ~m1_pre_topc('#skF_4', A_231) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231))), inference(resolution, [status(thm)], [c_175, c_22])).
% 9.51/3.09  tff(c_349, plain, (m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_335])).
% 9.51/3.09  tff(c_372, plain, (m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_82, c_120, c_85, c_349])).
% 9.51/3.09  tff(c_379, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_372])).
% 9.51/3.09  tff(c_382, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_379])).
% 9.51/3.09  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_382])).
% 9.51/3.09  tff(c_387, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_372])).
% 9.51/3.09  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_28, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_566, plain, (![E_255, C_256, B_254, A_253, D_252]: (k3_tmap_1(A_253, B_254, C_256, D_252, E_255)=k2_partfun1(u1_struct_0(C_256), u1_struct_0(B_254), E_255, u1_struct_0(D_252)) | ~m1_pre_topc(D_252, C_256) | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_256), u1_struct_0(B_254)))) | ~v1_funct_2(E_255, u1_struct_0(C_256), u1_struct_0(B_254)) | ~v1_funct_1(E_255) | ~m1_pre_topc(D_252, A_253) | ~m1_pre_topc(C_256, A_253) | ~l1_pre_topc(B_254) | ~v2_pre_topc(B_254) | v2_struct_0(B_254) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.51/3.09  tff(c_570, plain, (![A_253, D_252]: (k3_tmap_1(A_253, '#skF_2', '#skF_3', D_252, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_252)) | ~m1_pre_topc(D_252, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_252, A_253) | ~m1_pre_topc('#skF_3', A_253) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(resolution, [status(thm)], [c_26, c_566])).
% 9.51/3.09  tff(c_574, plain, (![A_253, D_252]: (k3_tmap_1(A_253, '#skF_2', '#skF_3', D_252, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_252)) | ~m1_pre_topc(D_252, '#skF_3') | ~m1_pre_topc(D_252, A_253) | ~m1_pre_topc('#skF_3', A_253) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_28, c_570])).
% 9.51/3.09  tff(c_576, plain, (![A_257, D_258]: (k3_tmap_1(A_257, '#skF_2', '#skF_3', D_258, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_258)) | ~m1_pre_topc(D_258, '#skF_3') | ~m1_pre_topc(D_258, A_257) | ~m1_pre_topc('#skF_3', A_257) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(negUnitSimplification, [status(thm)], [c_52, c_574])).
% 9.51/3.09  tff(c_592, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_576])).
% 9.51/3.09  tff(c_622, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_34, c_592])).
% 9.51/3.09  tff(c_623, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_622])).
% 9.51/3.09  tff(c_319, plain, (![A_225, B_226, C_227, D_228]: (k2_partfun1(u1_struct_0(A_225), u1_struct_0(B_226), C_227, u1_struct_0(D_228))=k2_tmap_1(A_225, B_226, C_227, D_228) | ~m1_pre_topc(D_228, A_225) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225), u1_struct_0(B_226)))) | ~v1_funct_2(C_227, u1_struct_0(A_225), u1_struct_0(B_226)) | ~v1_funct_1(C_227) | ~l1_pre_topc(B_226) | ~v2_pre_topc(B_226) | v2_struct_0(B_226) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.51/3.09  tff(c_321, plain, (![D_228]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_228))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_228) | ~m1_pre_topc(D_228, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_319])).
% 9.51/3.09  tff(c_324, plain, (![D_228]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_228))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_228) | ~m1_pre_topc(D_228, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_85, c_50, c_48, c_30, c_28, c_321])).
% 9.51/3.09  tff(c_325, plain, (![D_228]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_228))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_228) | ~m1_pre_topc(D_228, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_52, c_324])).
% 9.51/3.09  tff(c_643, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_623, c_325])).
% 9.51/3.09  tff(c_650, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_643])).
% 9.51/3.09  tff(c_189, plain, (![A_213, D_215, B_216, C_212, E_214]: (v1_funct_1(k3_tmap_1(A_213, B_216, C_212, D_215, E_214)) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212), u1_struct_0(B_216)))) | ~v1_funct_2(E_214, u1_struct_0(C_212), u1_struct_0(B_216)) | ~v1_funct_1(E_214) | ~m1_pre_topc(D_215, A_213) | ~m1_pre_topc(C_212, A_213) | ~l1_pre_topc(B_216) | ~v2_pre_topc(B_216) | v2_struct_0(B_216) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.51/3.09  tff(c_191, plain, (![A_213, D_215]: (v1_funct_1(k3_tmap_1(A_213, '#skF_2', '#skF_3', D_215, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_215, A_213) | ~m1_pre_topc('#skF_3', A_213) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(resolution, [status(thm)], [c_26, c_189])).
% 9.51/3.09  tff(c_194, plain, (![A_213, D_215]: (v1_funct_1(k3_tmap_1(A_213, '#skF_2', '#skF_3', D_215, '#skF_6')) | ~m1_pre_topc(D_215, A_213) | ~m1_pre_topc('#skF_3', A_213) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_28, c_191])).
% 9.51/3.09  tff(c_195, plain, (![A_213, D_215]: (v1_funct_1(k3_tmap_1(A_213, '#skF_2', '#skF_3', D_215, '#skF_6')) | ~m1_pre_topc(D_215, A_213) | ~m1_pre_topc('#skF_3', A_213) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(negUnitSimplification, [status(thm)], [c_52, c_194])).
% 9.51/3.09  tff(c_665, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_650, c_195])).
% 9.51/3.09  tff(c_675, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_40, c_665])).
% 9.51/3.09  tff(c_676, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_675])).
% 9.51/3.09  tff(c_537, plain, (![D_238, C_235, B_239, E_237, A_236]: (v1_funct_2(k3_tmap_1(A_236, B_239, C_235, D_238, E_237), u1_struct_0(D_238), u1_struct_0(B_239)) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_235), u1_struct_0(B_239)))) | ~v1_funct_2(E_237, u1_struct_0(C_235), u1_struct_0(B_239)) | ~v1_funct_1(E_237) | ~m1_pre_topc(D_238, A_236) | ~m1_pre_topc(C_235, A_236) | ~l1_pre_topc(B_239) | ~v2_pre_topc(B_239) | v2_struct_0(B_239) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.51/3.09  tff(c_539, plain, (![A_236, D_238]: (v1_funct_2(k3_tmap_1(A_236, '#skF_2', '#skF_3', D_238, '#skF_6'), u1_struct_0(D_238), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_238, A_236) | ~m1_pre_topc('#skF_3', A_236) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(resolution, [status(thm)], [c_26, c_537])).
% 9.51/3.09  tff(c_542, plain, (![A_236, D_238]: (v1_funct_2(k3_tmap_1(A_236, '#skF_2', '#skF_3', D_238, '#skF_6'), u1_struct_0(D_238), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_238, A_236) | ~m1_pre_topc('#skF_3', A_236) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_28, c_539])).
% 9.51/3.09  tff(c_543, plain, (![A_236, D_238]: (v1_funct_2(k3_tmap_1(A_236, '#skF_2', '#skF_3', D_238, '#skF_6'), u1_struct_0(D_238), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_238, A_236) | ~m1_pre_topc('#skF_3', A_236) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(negUnitSimplification, [status(thm)], [c_52, c_542])).
% 9.51/3.09  tff(c_662, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_650, c_543])).
% 9.51/3.09  tff(c_672, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_40, c_662])).
% 9.51/3.09  tff(c_673, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_672])).
% 9.51/3.09  tff(c_10, plain, (![A_53, D_56, E_57, C_55, B_54]: (m1_subset_1(k3_tmap_1(A_53, B_54, C_55, D_56, E_57), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_56), u1_struct_0(B_54)))) | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_55), u1_struct_0(B_54)))) | ~v1_funct_2(E_57, u1_struct_0(C_55), u1_struct_0(B_54)) | ~v1_funct_1(E_57) | ~m1_pre_topc(D_56, A_53) | ~m1_pre_topc(C_55, A_53) | ~l1_pre_topc(B_54) | ~v2_pre_topc(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.51/3.09  tff(c_659, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_650, c_10])).
% 9.51/3.09  tff(c_669, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_44, c_40, c_30, c_28, c_26, c_659])).
% 9.51/3.09  tff(c_670, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_669])).
% 9.51/3.09  tff(c_6, plain, (![A_7, B_15, C_19, D_21]: (k2_partfun1(u1_struct_0(A_7), u1_struct_0(B_15), C_19, u1_struct_0(D_21))=k2_tmap_1(A_7, B_15, C_19, D_21) | ~m1_pre_topc(D_21, A_7) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7), u1_struct_0(B_15)))) | ~v1_funct_2(C_19, u1_struct_0(A_7), u1_struct_0(B_15)) | ~v1_funct_1(C_19) | ~l1_pre_topc(B_15) | ~v2_pre_topc(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.51/3.09  tff(c_687, plain, (![D_21]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_21))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_21) | ~m1_pre_topc(D_21, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_670, c_6])).
% 9.51/3.09  tff(c_704, plain, (![D_21]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_21))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_21) | ~m1_pre_topc(D_21, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_82, c_50, c_48, c_676, c_673, c_687])).
% 9.51/3.09  tff(c_705, plain, (![D_21]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_21))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_21) | ~m1_pre_topc(D_21, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_52, c_704])).
% 9.51/3.09  tff(c_594, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_576])).
% 9.51/3.09  tff(c_626, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_594])).
% 9.51/3.09  tff(c_627, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_626])).
% 9.51/3.09  tff(c_829, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_627])).
% 9.51/3.09  tff(c_835, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_829])).
% 9.51/3.09  tff(c_842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_835])).
% 9.51/3.09  tff(c_844, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_627])).
% 9.51/3.09  tff(c_654, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_650, c_623])).
% 9.51/3.09  tff(c_596, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_576])).
% 9.51/3.09  tff(c_630, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_85, c_34, c_596])).
% 9.51/3.09  tff(c_631, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_630])).
% 9.51/3.09  tff(c_827, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_654, c_631])).
% 9.51/3.09  tff(c_828, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_827])).
% 9.51/3.09  tff(c_893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_844, c_828])).
% 9.51/3.09  tff(c_895, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_827])).
% 9.51/3.09  tff(c_894, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_827])).
% 9.51/3.09  tff(c_1369, plain, (![D_303, E_302, B_306, D_304, C_300, A_301, A_305]: (k3_tmap_1(A_305, B_306, D_304, D_303, k3_tmap_1(A_301, B_306, C_300, D_304, E_302))=k2_partfun1(u1_struct_0(D_304), u1_struct_0(B_306), k3_tmap_1(A_301, B_306, C_300, D_304, E_302), u1_struct_0(D_303)) | ~m1_pre_topc(D_303, D_304) | ~v1_funct_2(k3_tmap_1(A_301, B_306, C_300, D_304, E_302), u1_struct_0(D_304), u1_struct_0(B_306)) | ~v1_funct_1(k3_tmap_1(A_301, B_306, C_300, D_304, E_302)) | ~m1_pre_topc(D_303, A_305) | ~m1_pre_topc(D_304, A_305) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_300), u1_struct_0(B_306)))) | ~v1_funct_2(E_302, u1_struct_0(C_300), u1_struct_0(B_306)) | ~v1_funct_1(E_302) | ~m1_pre_topc(D_304, A_301) | ~m1_pre_topc(C_300, A_301) | ~l1_pre_topc(B_306) | ~v2_pre_topc(B_306) | v2_struct_0(B_306) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(resolution, [status(thm)], [c_10, c_566])).
% 9.51/3.09  tff(c_1379, plain, (![A_305, D_304, D_303, A_301]: (k3_tmap_1(A_305, '#skF_2', D_304, D_303, k3_tmap_1(A_301, '#skF_2', '#skF_3', D_304, '#skF_6'))=k2_partfun1(u1_struct_0(D_304), u1_struct_0('#skF_2'), k3_tmap_1(A_301, '#skF_2', '#skF_3', D_304, '#skF_6'), u1_struct_0(D_303)) | ~m1_pre_topc(D_303, D_304) | ~v1_funct_2(k3_tmap_1(A_301, '#skF_2', '#skF_3', D_304, '#skF_6'), u1_struct_0(D_304), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_301, '#skF_2', '#skF_3', D_304, '#skF_6')) | ~m1_pre_topc(D_303, A_305) | ~m1_pre_topc(D_304, A_305) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_304, A_301) | ~m1_pre_topc('#skF_3', A_301) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(resolution, [status(thm)], [c_26, c_1369])).
% 9.51/3.09  tff(c_1395, plain, (![A_305, D_304, D_303, A_301]: (k3_tmap_1(A_305, '#skF_2', D_304, D_303, k3_tmap_1(A_301, '#skF_2', '#skF_3', D_304, '#skF_6'))=k2_partfun1(u1_struct_0(D_304), u1_struct_0('#skF_2'), k3_tmap_1(A_301, '#skF_2', '#skF_3', D_304, '#skF_6'), u1_struct_0(D_303)) | ~m1_pre_topc(D_303, D_304) | ~v1_funct_2(k3_tmap_1(A_301, '#skF_2', '#skF_3', D_304, '#skF_6'), u1_struct_0(D_304), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_301, '#skF_2', '#skF_3', D_304, '#skF_6')) | ~m1_pre_topc(D_303, A_305) | ~m1_pre_topc(D_304, A_305) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305) | ~m1_pre_topc(D_304, A_301) | ~m1_pre_topc('#skF_3', A_301) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_28, c_1379])).
% 9.51/3.09  tff(c_1752, plain, (![A_333, D_334, D_335, A_336]: (k3_tmap_1(A_333, '#skF_2', D_334, D_335, k3_tmap_1(A_336, '#skF_2', '#skF_3', D_334, '#skF_6'))=k2_partfun1(u1_struct_0(D_334), u1_struct_0('#skF_2'), k3_tmap_1(A_336, '#skF_2', '#skF_3', D_334, '#skF_6'), u1_struct_0(D_335)) | ~m1_pre_topc(D_335, D_334) | ~v1_funct_2(k3_tmap_1(A_336, '#skF_2', '#skF_3', D_334, '#skF_6'), u1_struct_0(D_334), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_336, '#skF_2', '#skF_3', D_334, '#skF_6')) | ~m1_pre_topc(D_335, A_333) | ~m1_pre_topc(D_334, A_333) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333) | ~m1_pre_topc(D_334, A_336) | ~m1_pre_topc('#skF_3', A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(negUnitSimplification, [status(thm)], [c_52, c_1395])).
% 9.51/3.09  tff(c_1821, plain, (![A_333, D_335]: (k3_tmap_1(A_333, '#skF_2', '#skF_4', D_335, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), u1_struct_0(D_335)) | ~m1_pre_topc(D_335, '#skF_4') | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_6')) | ~m1_pre_topc(D_335, A_333) | ~m1_pre_topc('#skF_4', A_333) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333) | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_894, c_1752])).
% 9.51/3.09  tff(c_1879, plain, (![A_333, D_335]: (k3_tmap_1(A_333, '#skF_2', '#skF_4', D_335, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_335)) | ~m1_pre_topc(D_335, '#skF_4') | ~m1_pre_topc(D_335, A_333) | ~m1_pre_topc('#skF_4', A_333) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_85, c_895, c_34, c_676, c_894, c_673, c_894, c_894, c_1821])).
% 9.51/3.09  tff(c_2155, plain, (![A_353, D_354]: (k3_tmap_1(A_353, '#skF_2', '#skF_4', D_354, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_354)) | ~m1_pre_topc(D_354, '#skF_4') | ~m1_pre_topc(D_354, A_353) | ~m1_pre_topc('#skF_4', A_353) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353))), inference(negUnitSimplification, [status(thm)], [c_46, c_1879])).
% 9.51/3.09  tff(c_4371, plain, (![A_411, D_412]: (k3_tmap_1(A_411, '#skF_2', '#skF_4', D_412, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_412) | ~m1_pre_topc(D_412, '#skF_4') | ~m1_pre_topc(D_412, A_411) | ~m1_pre_topc('#skF_4', A_411) | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411) | ~m1_pre_topc(D_412, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_705, c_2155])).
% 9.51/3.09  tff(c_575, plain, (![A_253, D_252]: (k3_tmap_1(A_253, '#skF_2', '#skF_3', D_252, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_252)) | ~m1_pre_topc(D_252, '#skF_3') | ~m1_pre_topc(D_252, A_253) | ~m1_pre_topc('#skF_3', A_253) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(negUnitSimplification, [status(thm)], [c_52, c_574])).
% 9.51/3.09  tff(c_897, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_895, c_575])).
% 9.51/3.09  tff(c_919, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_85, c_895, c_897])).
% 9.51/3.09  tff(c_920, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_919])).
% 9.51/3.09  tff(c_995, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_920, c_325])).
% 9.51/3.09  tff(c_1002, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_895, c_995])).
% 9.51/3.09  tff(c_545, plain, (![C_242, B_243, D_244, A_245]: (r2_funct_2(u1_struct_0(C_242), u1_struct_0(B_243), D_244, k3_tmap_1(A_245, B_243, C_242, C_242, D_244)) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_242), u1_struct_0(B_243)))) | ~v1_funct_2(D_244, u1_struct_0(C_242), u1_struct_0(B_243)) | ~v1_funct_1(D_244) | ~m1_pre_topc(C_242, A_245) | v2_struct_0(C_242) | ~l1_pre_topc(B_243) | ~v2_pre_topc(B_243) | v2_struct_0(B_243) | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245))), inference(cnfTransformation, [status(thm)], [f_164])).
% 9.51/3.09  tff(c_547, plain, (![A_245]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k3_tmap_1(A_245, '#skF_2', '#skF_3', '#skF_3', '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_3', A_245) | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245))), inference(resolution, [status(thm)], [c_26, c_545])).
% 9.51/3.09  tff(c_550, plain, (![A_245]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k3_tmap_1(A_245, '#skF_2', '#skF_3', '#skF_3', '#skF_6')) | ~m1_pre_topc('#skF_3', A_245) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_28, c_547])).
% 9.51/3.09  tff(c_551, plain, (![A_245]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k3_tmap_1(A_245, '#skF_2', '#skF_3', '#skF_3', '#skF_6')) | ~m1_pre_topc('#skF_3', A_245) | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_550])).
% 9.51/3.09  tff(c_1018, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1002, c_551])).
% 9.51/3.09  tff(c_1037, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_85, c_895, c_1018])).
% 9.51/3.09  tff(c_1038, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1037])).
% 9.51/3.09  tff(c_20, plain, (![A_74, D_130, C_122, E_134, F_136, B_106]: (r2_funct_2(u1_struct_0(D_130), u1_struct_0(B_106), k3_tmap_1(A_74, B_106, C_122, D_130, F_136), k2_tmap_1(A_74, B_106, E_134, D_130)) | ~m1_pre_topc(D_130, C_122) | ~r2_funct_2(u1_struct_0(C_122), u1_struct_0(B_106), F_136, k2_tmap_1(A_74, B_106, E_134, C_122)) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_122), u1_struct_0(B_106)))) | ~v1_funct_2(F_136, u1_struct_0(C_122), u1_struct_0(B_106)) | ~v1_funct_1(F_136) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74), u1_struct_0(B_106)))) | ~v1_funct_2(E_134, u1_struct_0(A_74), u1_struct_0(B_106)) | ~v1_funct_1(E_134) | ~m1_pre_topc(D_130, A_74) | v2_struct_0(D_130) | ~m1_pre_topc(C_122, A_74) | v2_struct_0(C_122) | ~l1_pre_topc(B_106) | ~v2_pre_topc(B_106) | v2_struct_0(B_106) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_211])).
% 9.51/3.09  tff(c_1048, plain, (![D_130]: (r2_funct_2(u1_struct_0(D_130), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_3', D_130, '#skF_6'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_130)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_130, '#skF_3') | v2_struct_0(D_130) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1038, c_20])).
% 9.51/3.09  tff(c_1051, plain, (![D_130]: (r2_funct_2(u1_struct_0(D_130), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_3', D_130, '#skF_6'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_130)) | ~m1_pre_topc(D_130, '#skF_3') | v2_struct_0(D_130) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_85, c_50, c_48, c_895, c_30, c_28, c_26, c_1048])).
% 9.51/3.09  tff(c_1213, plain, (![D_285]: (r2_funct_2(u1_struct_0(D_285), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_3', D_285, '#skF_6'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_285)) | ~m1_pre_topc(D_285, '#skF_3') | v2_struct_0(D_285))), inference(negUnitSimplification, [status(thm)], [c_46, c_52, c_1051])).
% 9.51/3.09  tff(c_1224, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_894, c_1213])).
% 9.51/3.09  tff(c_1236, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1224])).
% 9.51/3.09  tff(c_1237, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_1236])).
% 9.51/3.09  tff(c_1251, plain, (![D_130]: (r2_funct_2(u1_struct_0(D_130), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_4', D_130, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_130)) | ~m1_pre_topc(D_130, '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_130, '#skF_3') | v2_struct_0(D_130) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1237, c_20])).
% 9.51/3.09  tff(c_1254, plain, (![D_130]: (r2_funct_2(u1_struct_0(D_130), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_4', D_130, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_130)) | ~m1_pre_topc(D_130, '#skF_4') | ~m1_pre_topc(D_130, '#skF_3') | v2_struct_0(D_130) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_85, c_50, c_48, c_34, c_30, c_28, c_26, c_676, c_673, c_670, c_1251])).
% 9.51/3.09  tff(c_1255, plain, (![D_130]: (r2_funct_2(u1_struct_0(D_130), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_4', D_130, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_130)) | ~m1_pre_topc(D_130, '#skF_4') | ~m1_pre_topc(D_130, '#skF_3') | v2_struct_0(D_130))), inference(negUnitSimplification, [status(thm)], [c_46, c_52, c_42, c_1254])).
% 9.51/3.09  tff(c_4408, plain, (![D_412]: (r2_funct_2(u1_struct_0(D_412), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_412), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_412)) | ~m1_pre_topc(D_412, '#skF_4') | ~m1_pre_topc(D_412, '#skF_3') | v2_struct_0(D_412) | ~m1_pre_topc(D_412, '#skF_4') | ~m1_pre_topc(D_412, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_412, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4371, c_1255])).
% 9.51/3.09  tff(c_4461, plain, (![D_412]: (r2_funct_2(u1_struct_0(D_412), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_412), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_412)) | v2_struct_0(D_412) | ~m1_pre_topc(D_412, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_412, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_85, c_34, c_4408])).
% 9.51/3.09  tff(c_4482, plain, (![D_413]: (r2_funct_2(u1_struct_0(D_413), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_413), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_413)) | v2_struct_0(D_413) | ~m1_pre_topc(D_413, '#skF_3') | ~m1_pre_topc(D_413, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_4461])).
% 9.51/3.09  tff(c_36, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_598, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_576])).
% 9.51/3.09  tff(c_634, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_387, c_598])).
% 9.51/3.09  tff(c_635, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_634])).
% 9.51/3.09  tff(c_713, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_635, c_325])).
% 9.51/3.09  tff(c_720, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_713])).
% 9.51/3.09  tff(c_24, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_270])).
% 9.51/3.09  tff(c_655, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_24])).
% 9.51/3.09  tff(c_1212, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_720, c_655])).
% 9.51/3.09  tff(c_4423, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4371, c_1212])).
% 9.51/3.09  tff(c_4470, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_56, c_54, c_40, c_36, c_32, c_4423])).
% 9.51/3.09  tff(c_4471, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_4470])).
% 9.51/3.09  tff(c_4485, plain, (v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4482, c_4471])).
% 9.51/3.09  tff(c_4490, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_387, c_4485])).
% 9.51/3.09  tff(c_4492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_4490])).
% 9.51/3.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.51/3.09  
% 9.51/3.09  Inference rules
% 9.51/3.09  ----------------------
% 9.51/3.09  #Ref     : 0
% 9.51/3.09  #Sup     : 817
% 9.51/3.09  #Fact    : 0
% 9.51/3.09  #Define  : 0
% 9.51/3.09  #Split   : 11
% 9.51/3.09  #Chain   : 0
% 9.51/3.09  #Close   : 0
% 9.51/3.09  
% 9.51/3.09  Ordering : KBO
% 9.51/3.09  
% 9.51/3.09  Simplification rules
% 9.51/3.09  ----------------------
% 9.51/3.09  #Subsume      : 138
% 9.51/3.09  #Demod        : 2774
% 9.51/3.09  #Tautology    : 180
% 9.51/3.09  #SimpNegUnit  : 487
% 9.51/3.09  #BackRed      : 4
% 9.51/3.09  
% 9.51/3.09  #Partial instantiations: 0
% 9.51/3.09  #Strategies tried      : 1
% 9.51/3.09  
% 9.51/3.09  Timing (in seconds)
% 9.51/3.09  ----------------------
% 9.51/3.09  Preprocessing        : 0.40
% 9.51/3.09  Parsing              : 0.21
% 9.51/3.10  CNF conversion       : 0.05
% 9.51/3.10  Main loop            : 1.90
% 9.51/3.10  Inferencing          : 0.53
% 9.51/3.10  Reduction            : 0.74
% 9.51/3.10  Demodulation         : 0.57
% 9.51/3.10  BG Simplification    : 0.07
% 9.51/3.10  Subsumption          : 0.49
% 9.51/3.10  Abstraction          : 0.13
% 9.51/3.10  MUC search           : 0.00
% 9.51/3.10  Cooper               : 0.00
% 9.51/3.10  Total                : 2.36
% 9.51/3.10  Index Insertion      : 0.00
% 9.51/3.10  Index Deletion       : 0.00
% 9.51/3.10  Index Matching       : 0.00
% 9.51/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
