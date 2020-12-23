%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:37 EST 2020

% Result     : Theorem 12.72s
% Output     : CNFRefutation 12.93s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 685 expanded)
%              Number of leaves         :   51 ( 257 expanded)
%              Depth                    :   16
%              Number of atoms          :  592 (3249 expanded)
%              Number of equality atoms :   43 ( 384 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_255,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & v5_pre_topc(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_borsuk_1(C,A,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( D = E
                           => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_216,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_155,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tdlat_3(B)
           => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc18_tex_2)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A) )
           => ( ~ v2_struct_0(B)
              & v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc35_tex_2)).

tff(f_178,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_46,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_75,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [B_114,A_115] :
      ( v1_xboole_0(B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_115))
      | ~ v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [A_3] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_109,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_111,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_12])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_64,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_56,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_52,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k1_tarski(A_4),k1_zfmisc_1(B_5))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_70,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_359,plain,(
    ! [C_187,A_188,B_189] :
      ( m1_subset_1(C_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(C_187,k1_zfmisc_1(u1_struct_0(B_189)))
      | ~ m1_pre_topc(B_189,A_188)
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_372,plain,(
    ! [A_190,A_191,B_192] :
      ( m1_subset_1(k1_tarski(A_190),k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ r2_hidden(A_190,u1_struct_0(B_192)) ) ),
    inference(resolution,[status(thm)],[c_8,c_359])).

tff(c_374,plain,(
    ! [A_190] :
      ( m1_subset_1(k1_tarski(A_190),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_190,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_372])).

tff(c_377,plain,(
    ! [A_190] :
      ( m1_subset_1(k1_tarski(A_190),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_190,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_374])).

tff(c_684,plain,(
    ! [A_257,B_258,C_259,E_260] :
      ( k8_relset_1(u1_struct_0(A_257),u1_struct_0(B_258),C_259,E_260) = k2_pre_topc(A_257,E_260)
      | ~ m1_subset_1(E_260,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ m1_subset_1(E_260,k1_zfmisc_1(u1_struct_0(B_258)))
      | ~ v3_borsuk_1(C_259,A_257,B_258)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_257),u1_struct_0(B_258))))
      | ~ v5_pre_topc(C_259,A_257,B_258)
      | ~ v1_funct_2(C_259,u1_struct_0(A_257),u1_struct_0(B_258))
      | ~ v1_funct_1(C_259)
      | ~ m1_pre_topc(B_258,A_257)
      | ~ v4_tex_2(B_258,A_257)
      | v2_struct_0(B_258)
      | ~ l1_pre_topc(A_257)
      | ~ v3_tdlat_3(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_694,plain,(
    ! [B_258,C_259,A_190] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_258),C_259,k1_tarski(A_190)) = k2_pre_topc('#skF_2',k1_tarski(A_190))
      | ~ m1_subset_1(k1_tarski(A_190),k1_zfmisc_1(u1_struct_0(B_258)))
      | ~ v3_borsuk_1(C_259,'#skF_2',B_258)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_258))))
      | ~ v5_pre_topc(C_259,'#skF_2',B_258)
      | ~ v1_funct_2(C_259,u1_struct_0('#skF_2'),u1_struct_0(B_258))
      | ~ v1_funct_1(C_259)
      | ~ m1_pre_topc(B_258,'#skF_2')
      | ~ v4_tex_2(B_258,'#skF_2')
      | v2_struct_0(B_258)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_190,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_377,c_684])).

tff(c_712,plain,(
    ! [B_258,C_259,A_190] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_258),C_259,k1_tarski(A_190)) = k2_pre_topc('#skF_2',k1_tarski(A_190))
      | ~ m1_subset_1(k1_tarski(A_190),k1_zfmisc_1(u1_struct_0(B_258)))
      | ~ v3_borsuk_1(C_259,'#skF_2',B_258)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_258))))
      | ~ v5_pre_topc(C_259,'#skF_2',B_258)
      | ~ v1_funct_2(C_259,u1_struct_0('#skF_2'),u1_struct_0(B_258))
      | ~ v1_funct_1(C_259)
      | ~ m1_pre_topc(B_258,'#skF_2')
      | ~ v4_tex_2(B_258,'#skF_2')
      | v2_struct_0(B_258)
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_190,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_694])).

tff(c_835,plain,(
    ! [B_306,C_307,A_308] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_306),C_307,k1_tarski(A_308)) = k2_pre_topc('#skF_2',k1_tarski(A_308))
      | ~ m1_subset_1(k1_tarski(A_308),k1_zfmisc_1(u1_struct_0(B_306)))
      | ~ v3_borsuk_1(C_307,'#skF_2',B_306)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_306))))
      | ~ v5_pre_topc(C_307,'#skF_2',B_306)
      | ~ v1_funct_2(C_307,u1_struct_0('#skF_2'),u1_struct_0(B_306))
      | ~ v1_funct_1(C_307)
      | ~ m1_pre_topc(B_306,'#skF_2')
      | ~ v4_tex_2(B_306,'#skF_2')
      | v2_struct_0(B_306)
      | ~ r2_hidden(A_308,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_712])).

tff(c_1337,plain,(
    ! [B_486,C_487,A_488] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_486),C_487,k1_tarski(A_488)) = k2_pre_topc('#skF_2',k1_tarski(A_488))
      | ~ v3_borsuk_1(C_487,'#skF_2',B_486)
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_486))))
      | ~ v5_pre_topc(C_487,'#skF_2',B_486)
      | ~ v1_funct_2(C_487,u1_struct_0('#skF_2'),u1_struct_0(B_486))
      | ~ v1_funct_1(C_487)
      | ~ m1_pre_topc(B_486,'#skF_2')
      | ~ v4_tex_2(B_486,'#skF_2')
      | v2_struct_0(B_486)
      | ~ r2_hidden(A_488,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_488,u1_struct_0(B_486)) ) ),
    inference(resolution,[status(thm)],[c_8,c_835])).

tff(c_1342,plain,(
    ! [A_488] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_488)) = k2_pre_topc('#skF_2',k1_tarski(A_488))
      | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ v4_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_488,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_1337])).

tff(c_1349,plain,(
    ! [A_488] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_488)) = k2_pre_topc('#skF_2',k1_tarski(A_488))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_488,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_52,c_1342])).

tff(c_1352,plain,(
    ! [A_489] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_489)) = k2_pre_topc('#skF_2',k1_tarski(A_489))
      | ~ r2_hidden(A_489,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1349])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( k6_domain_1(A_27,B_28) = k1_tarski(B_28)
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_140,plain,(
    ! [A_130,B_131] :
      ( k6_domain_1(A_130,B_131) = k1_tarski(B_131)
      | ~ m1_subset_1(B_131,A_130) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_22])).

tff(c_159,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_75,c_140])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_160,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_140])).

tff(c_44,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_76,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_273,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_76])).

tff(c_349,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_273])).

tff(c_1363,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1352,c_349])).

tff(c_1367,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_111,c_1363])).

tff(c_1371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1367])).

tff(c_1372,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_1383,plain,(
    ! [B_492,A_493] :
      ( v2_pre_topc(B_492)
      | ~ m1_pre_topc(B_492,A_493)
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1386,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1383])).

tff(c_1389,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1386])).

tff(c_92,plain,(
    ! [B_110,A_111] :
      ( l1_pre_topc(B_110)
      | ~ m1_pre_topc(B_110,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_95,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_92])).

tff(c_98,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_95])).

tff(c_1395,plain,(
    ! [A_496,B_497] :
      ( k6_domain_1(A_496,B_497) = k1_tarski(B_497)
      | ~ m1_subset_1(B_497,A_496)
      | v1_xboole_0(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1414,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_75,c_1395])).

tff(c_4721,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1414])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4725,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4721,c_2])).

tff(c_7143,plain,(
    ! [B_995,A_996] :
      ( ~ v3_tex_2(B_995,A_996)
      | ~ m1_subset_1(B_995,k1_zfmisc_1(u1_struct_0(A_996)))
      | ~ v1_xboole_0(B_995)
      | ~ l1_pre_topc(A_996)
      | ~ v2_pre_topc(A_996)
      | v2_struct_0(A_996) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_7152,plain,(
    ! [B_995] :
      ( ~ v3_tex_2(B_995,'#skF_3')
      | ~ m1_subset_1(B_995,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_995)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_7143])).

tff(c_7164,plain,(
    ! [B_995] :
      ( ~ v3_tex_2(B_995,'#skF_3')
      | ~ m1_subset_1(B_995,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_995)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_98,c_7152])).

tff(c_7180,plain,(
    ! [B_999] :
      ( ~ v3_tex_2(B_999,'#skF_3')
      | ~ m1_subset_1(B_999,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_999) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7164])).

tff(c_7191,plain,
    ( ~ v3_tex_2(k1_xboole_0,'#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_7180])).

tff(c_7196,plain,(
    ~ v3_tex_2(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_7191])).

tff(c_5768,plain,(
    ! [B_873,A_874] :
      ( v2_tex_2(B_873,A_874)
      | ~ m1_subset_1(B_873,k1_zfmisc_1(u1_struct_0(A_874)))
      | ~ v1_xboole_0(B_873)
      | ~ l1_pre_topc(A_874)
      | ~ v2_pre_topc(A_874)
      | v2_struct_0(A_874) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5777,plain,(
    ! [B_873] :
      ( v2_tex_2(B_873,'#skF_3')
      | ~ m1_subset_1(B_873,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_873)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_5768])).

tff(c_5789,plain,(
    ! [B_873] :
      ( v2_tex_2(B_873,'#skF_3')
      | ~ m1_subset_1(B_873,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_873)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_98,c_5777])).

tff(c_5796,plain,(
    ! [B_876] :
      ( v2_tex_2(B_876,'#skF_3')
      | ~ m1_subset_1(B_876,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_876) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5789])).

tff(c_5807,plain,
    ( v2_tex_2(k1_xboole_0,'#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_5796])).

tff(c_5812,plain,(
    v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_5807])).

tff(c_4842,plain,(
    ! [B_773,A_774] :
      ( v3_tdlat_3(B_773)
      | ~ v1_tdlat_3(B_773)
      | ~ m1_pre_topc(B_773,A_774)
      | ~ l1_pre_topc(A_774)
      | v2_struct_0(A_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4845,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_4842])).

tff(c_4848,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4845])).

tff(c_4849,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v1_tdlat_3('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4848])).

tff(c_4850,plain,(
    ~ v1_tdlat_3('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4849])).

tff(c_4886,plain,(
    ! [B_783,A_784] :
      ( v1_tdlat_3(B_783)
      | ~ v4_tex_2(B_783,A_784)
      | v2_struct_0(B_783)
      | ~ m1_pre_topc(B_783,A_784)
      | ~ l1_pre_topc(A_784)
      | v2_struct_0(A_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4889,plain,
    ( v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_4886])).

tff(c_4892,plain,
    ( v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_4889])).

tff(c_4894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_4850,c_4892])).

tff(c_4895,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4849])).

tff(c_7513,plain,(
    ! [A_1029,B_1030] :
      ( m1_subset_1('#skF_1'(A_1029,B_1030),k1_zfmisc_1(u1_struct_0(A_1029)))
      | ~ v2_tex_2(B_1030,A_1029)
      | ~ m1_subset_1(B_1030,k1_zfmisc_1(u1_struct_0(A_1029)))
      | ~ l1_pre_topc(A_1029)
      | ~ v3_tdlat_3(A_1029)
      | ~ v2_pre_topc(A_1029)
      | v2_struct_0(A_1029) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_7539,plain,(
    ! [B_1030] :
      ( m1_subset_1('#skF_1'('#skF_3',B_1030),k1_zfmisc_1(k1_xboole_0))
      | ~ v2_tex_2(B_1030,'#skF_3')
      | ~ m1_subset_1(B_1030,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_7513])).

tff(c_7552,plain,(
    ! [B_1030] :
      ( m1_subset_1('#skF_1'('#skF_3',B_1030),k1_zfmisc_1(k1_xboole_0))
      | ~ v2_tex_2(B_1030,'#skF_3')
      | ~ m1_subset_1(B_1030,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_4895,c_98,c_4725,c_7539])).

tff(c_7688,plain,(
    ! [B_1048] :
      ( m1_subset_1('#skF_1'('#skF_3',B_1048),k1_zfmisc_1(k1_xboole_0))
      | ~ v2_tex_2(B_1048,'#skF_3')
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7552])).

tff(c_10,plain,(
    ! [B_8,A_6] :
      ( v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7705,plain,(
    ! [B_1048] :
      ( v1_xboole_0('#skF_1'('#skF_3',B_1048))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v2_tex_2(B_1048,'#skF_3')
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_7688,c_10])).

tff(c_7765,plain,(
    ! [B_1052] :
      ( v1_xboole_0('#skF_1'('#skF_3',B_1052))
      | ~ v2_tex_2(B_1052,'#skF_3')
      | ~ m1_subset_1(B_1052,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_7705])).

tff(c_7779,plain,
    ( v1_xboole_0('#skF_1'('#skF_3',k1_xboole_0))
    | ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_7765])).

tff(c_7785,plain,(
    v1_xboole_0('#skF_1'('#skF_3',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5812,c_7779])).

tff(c_7789,plain,(
    '#skF_1'('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7785,c_2])).

tff(c_7368,plain,(
    ! [A_1020,B_1021] :
      ( v3_tex_2('#skF_1'(A_1020,B_1021),A_1020)
      | ~ v2_tex_2(B_1021,A_1020)
      | ~ m1_subset_1(B_1021,k1_zfmisc_1(u1_struct_0(A_1020)))
      | ~ l1_pre_topc(A_1020)
      | ~ v3_tdlat_3(A_1020)
      | ~ v2_pre_topc(A_1020)
      | v2_struct_0(A_1020) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_7378,plain,(
    ! [B_1021] :
      ( v3_tex_2('#skF_1'('#skF_3',B_1021),'#skF_3')
      | ~ v2_tex_2(B_1021,'#skF_3')
      | ~ m1_subset_1(B_1021,k1_zfmisc_1(k1_xboole_0))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_7368])).

tff(c_7393,plain,(
    ! [B_1021] :
      ( v3_tex_2('#skF_1'('#skF_3',B_1021),'#skF_3')
      | ~ v2_tex_2(B_1021,'#skF_3')
      | ~ m1_subset_1(B_1021,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_4895,c_98,c_7378])).

tff(c_7394,plain,(
    ! [B_1021] :
      ( v3_tex_2('#skF_1'('#skF_3',B_1021),'#skF_3')
      | ~ v2_tex_2(B_1021,'#skF_3')
      | ~ m1_subset_1(B_1021,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7393])).

tff(c_7807,plain,
    ( v3_tex_2(k1_xboole_0,'#skF_3')
    | ~ v2_tex_2(k1_xboole_0,'#skF_3')
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7789,c_7394])).

tff(c_7819,plain,(
    v3_tex_2(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5812,c_7807])).

tff(c_7821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7196,c_7819])).

tff(c_7823,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1414])).

tff(c_17420,plain,(
    ! [C_2338,A_2339,B_2340] :
      ( m1_subset_1(C_2338,k1_zfmisc_1(u1_struct_0(A_2339)))
      | ~ m1_subset_1(C_2338,k1_zfmisc_1(u1_struct_0(B_2340)))
      | ~ m1_pre_topc(B_2340,A_2339)
      | ~ l1_pre_topc(A_2339) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_17433,plain,(
    ! [A_2341,A_2342,B_2343] :
      ( m1_subset_1(k1_tarski(A_2341),k1_zfmisc_1(u1_struct_0(A_2342)))
      | ~ m1_pre_topc(B_2343,A_2342)
      | ~ l1_pre_topc(A_2342)
      | ~ r2_hidden(A_2341,u1_struct_0(B_2343)) ) ),
    inference(resolution,[status(thm)],[c_8,c_17420])).

tff(c_17435,plain,(
    ! [A_2341] :
      ( m1_subset_1(k1_tarski(A_2341),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_2341,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_17433])).

tff(c_17438,plain,(
    ! [A_2341] :
      ( m1_subset_1(k1_tarski(A_2341),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_2341,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_17435])).

tff(c_19047,plain,(
    ! [A_2569,B_2570,C_2571,E_2572] :
      ( k8_relset_1(u1_struct_0(A_2569),u1_struct_0(B_2570),C_2571,E_2572) = k2_pre_topc(A_2569,E_2572)
      | ~ m1_subset_1(E_2572,k1_zfmisc_1(u1_struct_0(A_2569)))
      | ~ m1_subset_1(E_2572,k1_zfmisc_1(u1_struct_0(B_2570)))
      | ~ v3_borsuk_1(C_2571,A_2569,B_2570)
      | ~ m1_subset_1(C_2571,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2569),u1_struct_0(B_2570))))
      | ~ v5_pre_topc(C_2571,A_2569,B_2570)
      | ~ v1_funct_2(C_2571,u1_struct_0(A_2569),u1_struct_0(B_2570))
      | ~ v1_funct_1(C_2571)
      | ~ m1_pre_topc(B_2570,A_2569)
      | ~ v4_tex_2(B_2570,A_2569)
      | v2_struct_0(B_2570)
      | ~ l1_pre_topc(A_2569)
      | ~ v3_tdlat_3(A_2569)
      | ~ v2_pre_topc(A_2569)
      | v2_struct_0(A_2569) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_19057,plain,(
    ! [B_2570,C_2571,A_2341] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_2570),C_2571,k1_tarski(A_2341)) = k2_pre_topc('#skF_2',k1_tarski(A_2341))
      | ~ m1_subset_1(k1_tarski(A_2341),k1_zfmisc_1(u1_struct_0(B_2570)))
      | ~ v3_borsuk_1(C_2571,'#skF_2',B_2570)
      | ~ m1_subset_1(C_2571,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_2570))))
      | ~ v5_pre_topc(C_2571,'#skF_2',B_2570)
      | ~ v1_funct_2(C_2571,u1_struct_0('#skF_2'),u1_struct_0(B_2570))
      | ~ v1_funct_1(C_2571)
      | ~ m1_pre_topc(B_2570,'#skF_2')
      | ~ v4_tex_2(B_2570,'#skF_2')
      | v2_struct_0(B_2570)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_2341,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_17438,c_19047])).

tff(c_19075,plain,(
    ! [B_2570,C_2571,A_2341] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_2570),C_2571,k1_tarski(A_2341)) = k2_pre_topc('#skF_2',k1_tarski(A_2341))
      | ~ m1_subset_1(k1_tarski(A_2341),k1_zfmisc_1(u1_struct_0(B_2570)))
      | ~ v3_borsuk_1(C_2571,'#skF_2',B_2570)
      | ~ m1_subset_1(C_2571,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_2570))))
      | ~ v5_pre_topc(C_2571,'#skF_2',B_2570)
      | ~ v1_funct_2(C_2571,u1_struct_0('#skF_2'),u1_struct_0(B_2570))
      | ~ v1_funct_1(C_2571)
      | ~ m1_pre_topc(B_2570,'#skF_2')
      | ~ v4_tex_2(B_2570,'#skF_2')
      | v2_struct_0(B_2570)
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_2341,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_19057])).

tff(c_19206,plain,(
    ! [B_2611,C_2612,A_2613] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_2611),C_2612,k1_tarski(A_2613)) = k2_pre_topc('#skF_2',k1_tarski(A_2613))
      | ~ m1_subset_1(k1_tarski(A_2613),k1_zfmisc_1(u1_struct_0(B_2611)))
      | ~ v3_borsuk_1(C_2612,'#skF_2',B_2611)
      | ~ m1_subset_1(C_2612,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_2611))))
      | ~ v5_pre_topc(C_2612,'#skF_2',B_2611)
      | ~ v1_funct_2(C_2612,u1_struct_0('#skF_2'),u1_struct_0(B_2611))
      | ~ v1_funct_1(C_2612)
      | ~ m1_pre_topc(B_2611,'#skF_2')
      | ~ v4_tex_2(B_2611,'#skF_2')
      | v2_struct_0(B_2611)
      | ~ r2_hidden(A_2613,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_19075])).

tff(c_19421,plain,(
    ! [B_2638,C_2639,A_2640] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_2638),C_2639,k1_tarski(A_2640)) = k2_pre_topc('#skF_2',k1_tarski(A_2640))
      | ~ v3_borsuk_1(C_2639,'#skF_2',B_2638)
      | ~ m1_subset_1(C_2639,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_2638))))
      | ~ v5_pre_topc(C_2639,'#skF_2',B_2638)
      | ~ v1_funct_2(C_2639,u1_struct_0('#skF_2'),u1_struct_0(B_2638))
      | ~ v1_funct_1(C_2639)
      | ~ m1_pre_topc(B_2638,'#skF_2')
      | ~ v4_tex_2(B_2638,'#skF_2')
      | v2_struct_0(B_2638)
      | ~ r2_hidden(A_2640,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_2640,u1_struct_0(B_2638)) ) ),
    inference(resolution,[status(thm)],[c_8,c_19206])).

tff(c_19426,plain,(
    ! [A_2640] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_2640)) = k2_pre_topc('#skF_2',k1_tarski(A_2640))
      | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ v4_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_2640,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_19421])).

tff(c_19433,plain,(
    ! [A_2640] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_2640)) = k2_pre_topc('#skF_2',k1_tarski(A_2640))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_2640,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_52,c_19426])).

tff(c_19436,plain,(
    ! [A_2641] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_2641)) = k2_pre_topc('#skF_2',k1_tarski(A_2641))
      | ~ r2_hidden(A_2641,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_19433])).

tff(c_7822,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1414])).

tff(c_1415,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_1395])).

tff(c_1421,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1415])).

tff(c_1425,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1421,c_2])).

tff(c_1881,plain,(
    ! [B_551,A_552] :
      ( ~ v3_tex_2(B_551,A_552)
      | ~ m1_subset_1(B_551,k1_zfmisc_1(u1_struct_0(A_552)))
      | ~ v1_xboole_0(B_551)
      | ~ l1_pre_topc(A_552)
      | ~ v2_pre_topc(A_552)
      | v2_struct_0(A_552) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1890,plain,(
    ! [B_551] :
      ( ~ v3_tex_2(B_551,'#skF_2')
      | ~ m1_subset_1(B_551,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_551)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_1881])).

tff(c_1904,plain,(
    ! [B_551] :
      ( ~ v3_tex_2(B_551,'#skF_2')
      | ~ m1_subset_1(B_551,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_551)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1890])).

tff(c_1932,plain,(
    ! [B_555] :
      ( ~ v3_tex_2(B_555,'#skF_2')
      | ~ m1_subset_1(B_555,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_555) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1904])).

tff(c_1946,plain,
    ( ~ v3_tex_2(k1_xboole_0,'#skF_2')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_1932])).

tff(c_1952,plain,(
    ~ v3_tex_2(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_1946])).

tff(c_1977,plain,(
    ! [B_560,A_561] :
      ( v2_tex_2(B_560,A_561)
      | ~ m1_subset_1(B_560,k1_zfmisc_1(u1_struct_0(A_561)))
      | ~ v1_xboole_0(B_560)
      | ~ l1_pre_topc(A_561)
      | ~ v2_pre_topc(A_561)
      | v2_struct_0(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1986,plain,(
    ! [B_560] :
      ( v2_tex_2(B_560,'#skF_2')
      | ~ m1_subset_1(B_560,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_560)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_1977])).

tff(c_2000,plain,(
    ! [B_560] :
      ( v2_tex_2(B_560,'#skF_2')
      | ~ m1_subset_1(B_560,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_560)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1986])).

tff(c_2028,plain,(
    ! [B_564] :
      ( v2_tex_2(B_564,'#skF_2')
      | ~ m1_subset_1(B_564,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_564) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2000])).

tff(c_2042,plain,
    ( v2_tex_2(k1_xboole_0,'#skF_2')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_2028])).

tff(c_2048,plain,(
    v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_2042])).

tff(c_4521,plain,(
    ! [A_754,B_755] :
      ( m1_subset_1('#skF_1'(A_754,B_755),k1_zfmisc_1(u1_struct_0(A_754)))
      | ~ v2_tex_2(B_755,A_754)
      | ~ m1_subset_1(B_755,k1_zfmisc_1(u1_struct_0(A_754)))
      | ~ l1_pre_topc(A_754)
      | ~ v3_tdlat_3(A_754)
      | ~ v2_pre_topc(A_754)
      | v2_struct_0(A_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4547,plain,(
    ! [B_755] :
      ( m1_subset_1('#skF_1'('#skF_2',B_755),k1_zfmisc_1(k1_xboole_0))
      | ~ v2_tex_2(B_755,'#skF_2')
      | ~ m1_subset_1(B_755,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_4521])).

tff(c_4560,plain,(
    ! [B_755] :
      ( m1_subset_1('#skF_1'('#skF_2',B_755),k1_zfmisc_1(k1_xboole_0))
      | ~ v2_tex_2(B_755,'#skF_2')
      | ~ m1_subset_1(B_755,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1425,c_4547])).

tff(c_4607,plain,(
    ! [B_761] :
      ( m1_subset_1('#skF_1'('#skF_2',B_761),k1_zfmisc_1(k1_xboole_0))
      | ~ v2_tex_2(B_761,'#skF_2')
      | ~ m1_subset_1(B_761,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4560])).

tff(c_4627,plain,(
    ! [B_761] :
      ( v1_xboole_0('#skF_1'('#skF_2',B_761))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v2_tex_2(B_761,'#skF_2')
      | ~ m1_subset_1(B_761,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4607,c_10])).

tff(c_4637,plain,(
    ! [B_762] :
      ( v1_xboole_0('#skF_1'('#skF_2',B_762))
      | ~ v2_tex_2(B_762,'#skF_2')
      | ~ m1_subset_1(B_762,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_4627])).

tff(c_4654,plain,
    ( v1_xboole_0('#skF_1'('#skF_2',k1_xboole_0))
    | ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_4637])).

tff(c_4661,plain,(
    v1_xboole_0('#skF_1'('#skF_2',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_4654])).

tff(c_4665,plain,(
    '#skF_1'('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4661,c_2])).

tff(c_2073,plain,(
    ! [A_569,B_570] :
      ( v3_tex_2('#skF_1'(A_569,B_570),A_569)
      | ~ v2_tex_2(B_570,A_569)
      | ~ m1_subset_1(B_570,k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ l1_pre_topc(A_569)
      | ~ v3_tdlat_3(A_569)
      | ~ v2_pre_topc(A_569)
      | v2_struct_0(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2079,plain,(
    ! [B_570] :
      ( v3_tex_2('#skF_1'('#skF_2',B_570),'#skF_2')
      | ~ v2_tex_2(B_570,'#skF_2')
      | ~ m1_subset_1(B_570,k1_zfmisc_1(k1_xboole_0))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_2073])).

tff(c_2091,plain,(
    ! [B_570] :
      ( v3_tex_2('#skF_1'('#skF_2',B_570),'#skF_2')
      | ~ v2_tex_2(B_570,'#skF_2')
      | ~ m1_subset_1(B_570,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_2079])).

tff(c_2092,plain,(
    ! [B_570] :
      ( v3_tex_2('#skF_1'('#skF_2',B_570),'#skF_2')
      | ~ v2_tex_2(B_570,'#skF_2')
      | ~ m1_subset_1(B_570,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2091])).

tff(c_4677,plain,
    ( v3_tex_2(k1_xboole_0,'#skF_2')
    | ~ v2_tex_2(k1_xboole_0,'#skF_2')
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4665,c_2092])).

tff(c_4688,plain,(
    v3_tex_2(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2048,c_4677])).

tff(c_4690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1952,c_4688])).

tff(c_4691,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1415])).

tff(c_4703,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4691,c_76])).

tff(c_17391,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7822,c_4703])).

tff(c_19447,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19436,c_17391])).

tff(c_19451,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_19447])).

tff(c_19454,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_19451])).

tff(c_19456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7823,c_19454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.72/5.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.72/5.09  
% 12.72/5.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.72/5.09  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 12.72/5.09  
% 12.72/5.09  %Foreground sorts:
% 12.72/5.09  
% 12.72/5.09  
% 12.72/5.09  %Background operators:
% 12.72/5.09  
% 12.72/5.09  
% 12.72/5.09  %Foreground operators:
% 12.72/5.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.72/5.09  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 12.72/5.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.72/5.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.72/5.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.72/5.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.72/5.09  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 12.72/5.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.72/5.09  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 12.72/5.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.72/5.09  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 12.72/5.09  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 12.72/5.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.72/5.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.72/5.09  tff('#skF_5', type, '#skF_5': $i).
% 12.72/5.09  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 12.72/5.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.72/5.09  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 12.72/5.09  tff('#skF_6', type, '#skF_6': $i).
% 12.72/5.09  tff('#skF_2', type, '#skF_2': $i).
% 12.72/5.09  tff('#skF_3', type, '#skF_3': $i).
% 12.72/5.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.72/5.09  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 12.72/5.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.72/5.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.72/5.09  tff('#skF_4', type, '#skF_4': $i).
% 12.72/5.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.72/5.09  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 12.72/5.09  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.72/5.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.72/5.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.72/5.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.72/5.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.72/5.09  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.72/5.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.72/5.09  
% 12.93/5.12  tff(f_255, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 12.93/5.12  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 12.93/5.12  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 12.93/5.12  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 12.93/5.12  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 12.93/5.12  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 12.93/5.12  tff(f_216, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 12.93/5.12  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 12.93/5.12  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 12.93/5.12  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 12.93/5.12  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 12.93/5.12  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 12.93/5.12  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 12.93/5.12  tff(f_108, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v1_tdlat_3(B) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc18_tex_2)).
% 12.93/5.12  tff(f_126, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & v4_tex_2(B, A)) => (~v2_struct_0(B) & v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc35_tex_2)).
% 12.93/5.12  tff(f_178, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 12.93/5.12  tff(c_46, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_75, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50])).
% 12.93/5.12  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.93/5.12  tff(c_100, plain, (![B_114, A_115]: (v1_xboole_0(B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(A_115)) | ~v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.93/5.12  tff(c_108, plain, (![A_3]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_100])).
% 12.93/5.12  tff(c_109, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitLeft, [status(thm)], [c_108])).
% 12.93/5.12  tff(c_12, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.93/5.12  tff(c_111, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | ~m1_subset_1(A_9, B_10))), inference(negUnitSimplification, [status(thm)], [c_109, c_12])).
% 12.93/5.12  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_64, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_56, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_52, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(k1_tarski(A_4), k1_zfmisc_1(B_5)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.93/5.12  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_70, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_359, plain, (![C_187, A_188, B_189]: (m1_subset_1(C_187, k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(C_187, k1_zfmisc_1(u1_struct_0(B_189))) | ~m1_pre_topc(B_189, A_188) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.93/5.12  tff(c_372, plain, (![A_190, A_191, B_192]: (m1_subset_1(k1_tarski(A_190), k1_zfmisc_1(u1_struct_0(A_191))) | ~m1_pre_topc(B_192, A_191) | ~l1_pre_topc(A_191) | ~r2_hidden(A_190, u1_struct_0(B_192)))), inference(resolution, [status(thm)], [c_8, c_359])).
% 12.93/5.12  tff(c_374, plain, (![A_190]: (m1_subset_1(k1_tarski(A_190), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_190, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_372])).
% 12.93/5.12  tff(c_377, plain, (![A_190]: (m1_subset_1(k1_tarski(A_190), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_190, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_374])).
% 12.93/5.12  tff(c_684, plain, (![A_257, B_258, C_259, E_260]: (k8_relset_1(u1_struct_0(A_257), u1_struct_0(B_258), C_259, E_260)=k2_pre_topc(A_257, E_260) | ~m1_subset_1(E_260, k1_zfmisc_1(u1_struct_0(A_257))) | ~m1_subset_1(E_260, k1_zfmisc_1(u1_struct_0(B_258))) | ~v3_borsuk_1(C_259, A_257, B_258) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_257), u1_struct_0(B_258)))) | ~v5_pre_topc(C_259, A_257, B_258) | ~v1_funct_2(C_259, u1_struct_0(A_257), u1_struct_0(B_258)) | ~v1_funct_1(C_259) | ~m1_pre_topc(B_258, A_257) | ~v4_tex_2(B_258, A_257) | v2_struct_0(B_258) | ~l1_pre_topc(A_257) | ~v3_tdlat_3(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(cnfTransformation, [status(thm)], [f_216])).
% 12.93/5.12  tff(c_694, plain, (![B_258, C_259, A_190]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_258), C_259, k1_tarski(A_190))=k2_pre_topc('#skF_2', k1_tarski(A_190)) | ~m1_subset_1(k1_tarski(A_190), k1_zfmisc_1(u1_struct_0(B_258))) | ~v3_borsuk_1(C_259, '#skF_2', B_258) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_258)))) | ~v5_pre_topc(C_259, '#skF_2', B_258) | ~v1_funct_2(C_259, u1_struct_0('#skF_2'), u1_struct_0(B_258)) | ~v1_funct_1(C_259) | ~m1_pre_topc(B_258, '#skF_2') | ~v4_tex_2(B_258, '#skF_2') | v2_struct_0(B_258) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(A_190, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_377, c_684])).
% 12.93/5.12  tff(c_712, plain, (![B_258, C_259, A_190]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_258), C_259, k1_tarski(A_190))=k2_pre_topc('#skF_2', k1_tarski(A_190)) | ~m1_subset_1(k1_tarski(A_190), k1_zfmisc_1(u1_struct_0(B_258))) | ~v3_borsuk_1(C_259, '#skF_2', B_258) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_258)))) | ~v5_pre_topc(C_259, '#skF_2', B_258) | ~v1_funct_2(C_259, u1_struct_0('#skF_2'), u1_struct_0(B_258)) | ~v1_funct_1(C_259) | ~m1_pre_topc(B_258, '#skF_2') | ~v4_tex_2(B_258, '#skF_2') | v2_struct_0(B_258) | v2_struct_0('#skF_2') | ~r2_hidden(A_190, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_694])).
% 12.93/5.12  tff(c_835, plain, (![B_306, C_307, A_308]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_306), C_307, k1_tarski(A_308))=k2_pre_topc('#skF_2', k1_tarski(A_308)) | ~m1_subset_1(k1_tarski(A_308), k1_zfmisc_1(u1_struct_0(B_306))) | ~v3_borsuk_1(C_307, '#skF_2', B_306) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_306)))) | ~v5_pre_topc(C_307, '#skF_2', B_306) | ~v1_funct_2(C_307, u1_struct_0('#skF_2'), u1_struct_0(B_306)) | ~v1_funct_1(C_307) | ~m1_pre_topc(B_306, '#skF_2') | ~v4_tex_2(B_306, '#skF_2') | v2_struct_0(B_306) | ~r2_hidden(A_308, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_74, c_712])).
% 12.93/5.12  tff(c_1337, plain, (![B_486, C_487, A_488]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_486), C_487, k1_tarski(A_488))=k2_pre_topc('#skF_2', k1_tarski(A_488)) | ~v3_borsuk_1(C_487, '#skF_2', B_486) | ~m1_subset_1(C_487, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_486)))) | ~v5_pre_topc(C_487, '#skF_2', B_486) | ~v1_funct_2(C_487, u1_struct_0('#skF_2'), u1_struct_0(B_486)) | ~v1_funct_1(C_487) | ~m1_pre_topc(B_486, '#skF_2') | ~v4_tex_2(B_486, '#skF_2') | v2_struct_0(B_486) | ~r2_hidden(A_488, u1_struct_0('#skF_3')) | ~r2_hidden(A_488, u1_struct_0(B_486)))), inference(resolution, [status(thm)], [c_8, c_835])).
% 12.93/5.12  tff(c_1342, plain, (![A_488]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_488))=k2_pre_topc('#skF_2', k1_tarski(A_488)) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~r2_hidden(A_488, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_1337])).
% 12.93/5.12  tff(c_1349, plain, (![A_488]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_488))=k2_pre_topc('#skF_2', k1_tarski(A_488)) | v2_struct_0('#skF_3') | ~r2_hidden(A_488, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_52, c_1342])).
% 12.93/5.12  tff(c_1352, plain, (![A_489]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_489))=k2_pre_topc('#skF_2', k1_tarski(A_489)) | ~r2_hidden(A_489, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1349])).
% 12.93/5.12  tff(c_22, plain, (![A_27, B_28]: (k6_domain_1(A_27, B_28)=k1_tarski(B_28) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.93/5.12  tff(c_140, plain, (![A_130, B_131]: (k6_domain_1(A_130, B_131)=k1_tarski(B_131) | ~m1_subset_1(B_131, A_130))), inference(negUnitSimplification, [status(thm)], [c_109, c_22])).
% 12.93/5.12  tff(c_159, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_75, c_140])).
% 12.93/5.12  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_160, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_48, c_140])).
% 12.93/5.12  tff(c_44, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 12.93/5.12  tff(c_76, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 12.93/5.12  tff(c_273, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_76])).
% 12.93/5.12  tff(c_349, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_273])).
% 12.93/5.12  tff(c_1363, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1352, c_349])).
% 12.93/5.12  tff(c_1367, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_111, c_1363])).
% 12.93/5.12  tff(c_1371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_1367])).
% 12.93/5.12  tff(c_1372, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_108])).
% 12.93/5.12  tff(c_1383, plain, (![B_492, A_493]: (v2_pre_topc(B_492) | ~m1_pre_topc(B_492, A_493) | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.93/5.12  tff(c_1386, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1383])).
% 12.93/5.12  tff(c_1389, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1386])).
% 12.93/5.12  tff(c_92, plain, (![B_110, A_111]: (l1_pre_topc(B_110) | ~m1_pre_topc(B_110, A_111) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.93/5.12  tff(c_95, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_92])).
% 12.93/5.12  tff(c_98, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_95])).
% 12.93/5.12  tff(c_1395, plain, (![A_496, B_497]: (k6_domain_1(A_496, B_497)=k1_tarski(B_497) | ~m1_subset_1(B_497, A_496) | v1_xboole_0(A_496))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.93/5.12  tff(c_1414, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_75, c_1395])).
% 12.93/5.12  tff(c_4721, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1414])).
% 12.93/5.12  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.93/5.12  tff(c_4725, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_4721, c_2])).
% 12.93/5.12  tff(c_7143, plain, (![B_995, A_996]: (~v3_tex_2(B_995, A_996) | ~m1_subset_1(B_995, k1_zfmisc_1(u1_struct_0(A_996))) | ~v1_xboole_0(B_995) | ~l1_pre_topc(A_996) | ~v2_pre_topc(A_996) | v2_struct_0(A_996))), inference(cnfTransformation, [status(thm)], [f_155])).
% 12.93/5.12  tff(c_7152, plain, (![B_995]: (~v3_tex_2(B_995, '#skF_3') | ~m1_subset_1(B_995, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_995) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_7143])).
% 12.93/5.12  tff(c_7164, plain, (![B_995]: (~v3_tex_2(B_995, '#skF_3') | ~m1_subset_1(B_995, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_995) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_98, c_7152])).
% 12.93/5.12  tff(c_7180, plain, (![B_999]: (~v3_tex_2(B_999, '#skF_3') | ~m1_subset_1(B_999, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_999))), inference(negUnitSimplification, [status(thm)], [c_66, c_7164])).
% 12.93/5.12  tff(c_7191, plain, (~v3_tex_2(k1_xboole_0, '#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_7180])).
% 12.93/5.12  tff(c_7196, plain, (~v3_tex_2(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_7191])).
% 12.93/5.12  tff(c_5768, plain, (![B_873, A_874]: (v2_tex_2(B_873, A_874) | ~m1_subset_1(B_873, k1_zfmisc_1(u1_struct_0(A_874))) | ~v1_xboole_0(B_873) | ~l1_pre_topc(A_874) | ~v2_pre_topc(A_874) | v2_struct_0(A_874))), inference(cnfTransformation, [status(thm)], [f_140])).
% 12.93/5.12  tff(c_5777, plain, (![B_873]: (v2_tex_2(B_873, '#skF_3') | ~m1_subset_1(B_873, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_873) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_5768])).
% 12.93/5.12  tff(c_5789, plain, (![B_873]: (v2_tex_2(B_873, '#skF_3') | ~m1_subset_1(B_873, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_873) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_98, c_5777])).
% 12.93/5.12  tff(c_5796, plain, (![B_876]: (v2_tex_2(B_876, '#skF_3') | ~m1_subset_1(B_876, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_876))), inference(negUnitSimplification, [status(thm)], [c_66, c_5789])).
% 12.93/5.12  tff(c_5807, plain, (v2_tex_2(k1_xboole_0, '#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_5796])).
% 12.93/5.12  tff(c_5812, plain, (v2_tex_2(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_5807])).
% 12.93/5.12  tff(c_4842, plain, (![B_773, A_774]: (v3_tdlat_3(B_773) | ~v1_tdlat_3(B_773) | ~m1_pre_topc(B_773, A_774) | ~l1_pre_topc(A_774) | v2_struct_0(A_774))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.93/5.12  tff(c_4845, plain, (v3_tdlat_3('#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_4842])).
% 12.93/5.12  tff(c_4848, plain, (v3_tdlat_3('#skF_3') | ~v1_tdlat_3('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4845])).
% 12.93/5.12  tff(c_4849, plain, (v3_tdlat_3('#skF_3') | ~v1_tdlat_3('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_4848])).
% 12.93/5.12  tff(c_4850, plain, (~v1_tdlat_3('#skF_3')), inference(splitLeft, [status(thm)], [c_4849])).
% 12.93/5.12  tff(c_4886, plain, (![B_783, A_784]: (v1_tdlat_3(B_783) | ~v4_tex_2(B_783, A_784) | v2_struct_0(B_783) | ~m1_pre_topc(B_783, A_784) | ~l1_pre_topc(A_784) | v2_struct_0(A_784))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.93/5.12  tff(c_4889, plain, (v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_4886])).
% 12.93/5.12  tff(c_4892, plain, (v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_4889])).
% 12.93/5.12  tff(c_4894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_4850, c_4892])).
% 12.93/5.12  tff(c_4895, plain, (v3_tdlat_3('#skF_3')), inference(splitRight, [status(thm)], [c_4849])).
% 12.93/5.12  tff(c_7513, plain, (![A_1029, B_1030]: (m1_subset_1('#skF_1'(A_1029, B_1030), k1_zfmisc_1(u1_struct_0(A_1029))) | ~v2_tex_2(B_1030, A_1029) | ~m1_subset_1(B_1030, k1_zfmisc_1(u1_struct_0(A_1029))) | ~l1_pre_topc(A_1029) | ~v3_tdlat_3(A_1029) | ~v2_pre_topc(A_1029) | v2_struct_0(A_1029))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.93/5.12  tff(c_7539, plain, (![B_1030]: (m1_subset_1('#skF_1'('#skF_3', B_1030), k1_zfmisc_1(k1_xboole_0)) | ~v2_tex_2(B_1030, '#skF_3') | ~m1_subset_1(B_1030, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_7513])).
% 12.93/5.12  tff(c_7552, plain, (![B_1030]: (m1_subset_1('#skF_1'('#skF_3', B_1030), k1_zfmisc_1(k1_xboole_0)) | ~v2_tex_2(B_1030, '#skF_3') | ~m1_subset_1(B_1030, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_4895, c_98, c_4725, c_7539])).
% 12.93/5.12  tff(c_7688, plain, (![B_1048]: (m1_subset_1('#skF_1'('#skF_3', B_1048), k1_zfmisc_1(k1_xboole_0)) | ~v2_tex_2(B_1048, '#skF_3') | ~m1_subset_1(B_1048, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_66, c_7552])).
% 12.93/5.12  tff(c_10, plain, (![B_8, A_6]: (v1_xboole_0(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.93/5.12  tff(c_7705, plain, (![B_1048]: (v1_xboole_0('#skF_1'('#skF_3', B_1048)) | ~v1_xboole_0(k1_xboole_0) | ~v2_tex_2(B_1048, '#skF_3') | ~m1_subset_1(B_1048, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_7688, c_10])).
% 12.93/5.12  tff(c_7765, plain, (![B_1052]: (v1_xboole_0('#skF_1'('#skF_3', B_1052)) | ~v2_tex_2(B_1052, '#skF_3') | ~m1_subset_1(B_1052, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_7705])).
% 12.93/5.12  tff(c_7779, plain, (v1_xboole_0('#skF_1'('#skF_3', k1_xboole_0)) | ~v2_tex_2(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_6, c_7765])).
% 12.93/5.12  tff(c_7785, plain, (v1_xboole_0('#skF_1'('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5812, c_7779])).
% 12.93/5.12  tff(c_7789, plain, ('#skF_1'('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_7785, c_2])).
% 12.93/5.12  tff(c_7368, plain, (![A_1020, B_1021]: (v3_tex_2('#skF_1'(A_1020, B_1021), A_1020) | ~v2_tex_2(B_1021, A_1020) | ~m1_subset_1(B_1021, k1_zfmisc_1(u1_struct_0(A_1020))) | ~l1_pre_topc(A_1020) | ~v3_tdlat_3(A_1020) | ~v2_pre_topc(A_1020) | v2_struct_0(A_1020))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.93/5.12  tff(c_7378, plain, (![B_1021]: (v3_tex_2('#skF_1'('#skF_3', B_1021), '#skF_3') | ~v2_tex_2(B_1021, '#skF_3') | ~m1_subset_1(B_1021, k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_7368])).
% 12.93/5.12  tff(c_7393, plain, (![B_1021]: (v3_tex_2('#skF_1'('#skF_3', B_1021), '#skF_3') | ~v2_tex_2(B_1021, '#skF_3') | ~m1_subset_1(B_1021, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_4895, c_98, c_7378])).
% 12.93/5.12  tff(c_7394, plain, (![B_1021]: (v3_tex_2('#skF_1'('#skF_3', B_1021), '#skF_3') | ~v2_tex_2(B_1021, '#skF_3') | ~m1_subset_1(B_1021, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_66, c_7393])).
% 12.93/5.12  tff(c_7807, plain, (v3_tex_2(k1_xboole_0, '#skF_3') | ~v2_tex_2(k1_xboole_0, '#skF_3') | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7789, c_7394])).
% 12.93/5.12  tff(c_7819, plain, (v3_tex_2(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5812, c_7807])).
% 12.93/5.12  tff(c_7821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7196, c_7819])).
% 12.93/5.12  tff(c_7823, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1414])).
% 12.93/5.12  tff(c_17420, plain, (![C_2338, A_2339, B_2340]: (m1_subset_1(C_2338, k1_zfmisc_1(u1_struct_0(A_2339))) | ~m1_subset_1(C_2338, k1_zfmisc_1(u1_struct_0(B_2340))) | ~m1_pre_topc(B_2340, A_2339) | ~l1_pre_topc(A_2339))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.93/5.12  tff(c_17433, plain, (![A_2341, A_2342, B_2343]: (m1_subset_1(k1_tarski(A_2341), k1_zfmisc_1(u1_struct_0(A_2342))) | ~m1_pre_topc(B_2343, A_2342) | ~l1_pre_topc(A_2342) | ~r2_hidden(A_2341, u1_struct_0(B_2343)))), inference(resolution, [status(thm)], [c_8, c_17420])).
% 12.93/5.12  tff(c_17435, plain, (![A_2341]: (m1_subset_1(k1_tarski(A_2341), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_2341, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_17433])).
% 12.93/5.12  tff(c_17438, plain, (![A_2341]: (m1_subset_1(k1_tarski(A_2341), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_2341, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_17435])).
% 12.93/5.12  tff(c_19047, plain, (![A_2569, B_2570, C_2571, E_2572]: (k8_relset_1(u1_struct_0(A_2569), u1_struct_0(B_2570), C_2571, E_2572)=k2_pre_topc(A_2569, E_2572) | ~m1_subset_1(E_2572, k1_zfmisc_1(u1_struct_0(A_2569))) | ~m1_subset_1(E_2572, k1_zfmisc_1(u1_struct_0(B_2570))) | ~v3_borsuk_1(C_2571, A_2569, B_2570) | ~m1_subset_1(C_2571, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2569), u1_struct_0(B_2570)))) | ~v5_pre_topc(C_2571, A_2569, B_2570) | ~v1_funct_2(C_2571, u1_struct_0(A_2569), u1_struct_0(B_2570)) | ~v1_funct_1(C_2571) | ~m1_pre_topc(B_2570, A_2569) | ~v4_tex_2(B_2570, A_2569) | v2_struct_0(B_2570) | ~l1_pre_topc(A_2569) | ~v3_tdlat_3(A_2569) | ~v2_pre_topc(A_2569) | v2_struct_0(A_2569))), inference(cnfTransformation, [status(thm)], [f_216])).
% 12.93/5.12  tff(c_19057, plain, (![B_2570, C_2571, A_2341]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_2570), C_2571, k1_tarski(A_2341))=k2_pre_topc('#skF_2', k1_tarski(A_2341)) | ~m1_subset_1(k1_tarski(A_2341), k1_zfmisc_1(u1_struct_0(B_2570))) | ~v3_borsuk_1(C_2571, '#skF_2', B_2570) | ~m1_subset_1(C_2571, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_2570)))) | ~v5_pre_topc(C_2571, '#skF_2', B_2570) | ~v1_funct_2(C_2571, u1_struct_0('#skF_2'), u1_struct_0(B_2570)) | ~v1_funct_1(C_2571) | ~m1_pre_topc(B_2570, '#skF_2') | ~v4_tex_2(B_2570, '#skF_2') | v2_struct_0(B_2570) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(A_2341, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_17438, c_19047])).
% 12.93/5.12  tff(c_19075, plain, (![B_2570, C_2571, A_2341]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_2570), C_2571, k1_tarski(A_2341))=k2_pre_topc('#skF_2', k1_tarski(A_2341)) | ~m1_subset_1(k1_tarski(A_2341), k1_zfmisc_1(u1_struct_0(B_2570))) | ~v3_borsuk_1(C_2571, '#skF_2', B_2570) | ~m1_subset_1(C_2571, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_2570)))) | ~v5_pre_topc(C_2571, '#skF_2', B_2570) | ~v1_funct_2(C_2571, u1_struct_0('#skF_2'), u1_struct_0(B_2570)) | ~v1_funct_1(C_2571) | ~m1_pre_topc(B_2570, '#skF_2') | ~v4_tex_2(B_2570, '#skF_2') | v2_struct_0(B_2570) | v2_struct_0('#skF_2') | ~r2_hidden(A_2341, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_19057])).
% 12.93/5.12  tff(c_19206, plain, (![B_2611, C_2612, A_2613]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_2611), C_2612, k1_tarski(A_2613))=k2_pre_topc('#skF_2', k1_tarski(A_2613)) | ~m1_subset_1(k1_tarski(A_2613), k1_zfmisc_1(u1_struct_0(B_2611))) | ~v3_borsuk_1(C_2612, '#skF_2', B_2611) | ~m1_subset_1(C_2612, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_2611)))) | ~v5_pre_topc(C_2612, '#skF_2', B_2611) | ~v1_funct_2(C_2612, u1_struct_0('#skF_2'), u1_struct_0(B_2611)) | ~v1_funct_1(C_2612) | ~m1_pre_topc(B_2611, '#skF_2') | ~v4_tex_2(B_2611, '#skF_2') | v2_struct_0(B_2611) | ~r2_hidden(A_2613, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_74, c_19075])).
% 12.93/5.12  tff(c_19421, plain, (![B_2638, C_2639, A_2640]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_2638), C_2639, k1_tarski(A_2640))=k2_pre_topc('#skF_2', k1_tarski(A_2640)) | ~v3_borsuk_1(C_2639, '#skF_2', B_2638) | ~m1_subset_1(C_2639, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_2638)))) | ~v5_pre_topc(C_2639, '#skF_2', B_2638) | ~v1_funct_2(C_2639, u1_struct_0('#skF_2'), u1_struct_0(B_2638)) | ~v1_funct_1(C_2639) | ~m1_pre_topc(B_2638, '#skF_2') | ~v4_tex_2(B_2638, '#skF_2') | v2_struct_0(B_2638) | ~r2_hidden(A_2640, u1_struct_0('#skF_3')) | ~r2_hidden(A_2640, u1_struct_0(B_2638)))), inference(resolution, [status(thm)], [c_8, c_19206])).
% 12.93/5.12  tff(c_19426, plain, (![A_2640]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_2640))=k2_pre_topc('#skF_2', k1_tarski(A_2640)) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~r2_hidden(A_2640, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_19421])).
% 12.93/5.12  tff(c_19433, plain, (![A_2640]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_2640))=k2_pre_topc('#skF_2', k1_tarski(A_2640)) | v2_struct_0('#skF_3') | ~r2_hidden(A_2640, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_52, c_19426])).
% 12.93/5.12  tff(c_19436, plain, (![A_2641]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_2641))=k2_pre_topc('#skF_2', k1_tarski(A_2641)) | ~r2_hidden(A_2641, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_19433])).
% 12.93/5.12  tff(c_7822, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_1414])).
% 12.93/5.12  tff(c_1415, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_1395])).
% 12.93/5.12  tff(c_1421, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1415])).
% 12.93/5.12  tff(c_1425, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1421, c_2])).
% 12.93/5.12  tff(c_1881, plain, (![B_551, A_552]: (~v3_tex_2(B_551, A_552) | ~m1_subset_1(B_551, k1_zfmisc_1(u1_struct_0(A_552))) | ~v1_xboole_0(B_551) | ~l1_pre_topc(A_552) | ~v2_pre_topc(A_552) | v2_struct_0(A_552))), inference(cnfTransformation, [status(thm)], [f_155])).
% 12.93/5.12  tff(c_1890, plain, (![B_551]: (~v3_tex_2(B_551, '#skF_2') | ~m1_subset_1(B_551, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_551) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1425, c_1881])).
% 12.93/5.12  tff(c_1904, plain, (![B_551]: (~v3_tex_2(B_551, '#skF_2') | ~m1_subset_1(B_551, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_551) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1890])).
% 12.93/5.12  tff(c_1932, plain, (![B_555]: (~v3_tex_2(B_555, '#skF_2') | ~m1_subset_1(B_555, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_555))), inference(negUnitSimplification, [status(thm)], [c_74, c_1904])).
% 12.93/5.12  tff(c_1946, plain, (~v3_tex_2(k1_xboole_0, '#skF_2') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1932])).
% 12.93/5.12  tff(c_1952, plain, (~v3_tex_2(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_1946])).
% 12.93/5.12  tff(c_1977, plain, (![B_560, A_561]: (v2_tex_2(B_560, A_561) | ~m1_subset_1(B_560, k1_zfmisc_1(u1_struct_0(A_561))) | ~v1_xboole_0(B_560) | ~l1_pre_topc(A_561) | ~v2_pre_topc(A_561) | v2_struct_0(A_561))), inference(cnfTransformation, [status(thm)], [f_140])).
% 12.93/5.12  tff(c_1986, plain, (![B_560]: (v2_tex_2(B_560, '#skF_2') | ~m1_subset_1(B_560, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_560) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1425, c_1977])).
% 12.93/5.12  tff(c_2000, plain, (![B_560]: (v2_tex_2(B_560, '#skF_2') | ~m1_subset_1(B_560, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_560) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1986])).
% 12.93/5.12  tff(c_2028, plain, (![B_564]: (v2_tex_2(B_564, '#skF_2') | ~m1_subset_1(B_564, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_564))), inference(negUnitSimplification, [status(thm)], [c_74, c_2000])).
% 12.93/5.12  tff(c_2042, plain, (v2_tex_2(k1_xboole_0, '#skF_2') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2028])).
% 12.93/5.12  tff(c_2048, plain, (v2_tex_2(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_2042])).
% 12.93/5.12  tff(c_4521, plain, (![A_754, B_755]: (m1_subset_1('#skF_1'(A_754, B_755), k1_zfmisc_1(u1_struct_0(A_754))) | ~v2_tex_2(B_755, A_754) | ~m1_subset_1(B_755, k1_zfmisc_1(u1_struct_0(A_754))) | ~l1_pre_topc(A_754) | ~v3_tdlat_3(A_754) | ~v2_pre_topc(A_754) | v2_struct_0(A_754))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.93/5.12  tff(c_4547, plain, (![B_755]: (m1_subset_1('#skF_1'('#skF_2', B_755), k1_zfmisc_1(k1_xboole_0)) | ~v2_tex_2(B_755, '#skF_2') | ~m1_subset_1(B_755, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1425, c_4521])).
% 12.93/5.12  tff(c_4560, plain, (![B_755]: (m1_subset_1('#skF_1'('#skF_2', B_755), k1_zfmisc_1(k1_xboole_0)) | ~v2_tex_2(B_755, '#skF_2') | ~m1_subset_1(B_755, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1425, c_4547])).
% 12.93/5.12  tff(c_4607, plain, (![B_761]: (m1_subset_1('#skF_1'('#skF_2', B_761), k1_zfmisc_1(k1_xboole_0)) | ~v2_tex_2(B_761, '#skF_2') | ~m1_subset_1(B_761, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_74, c_4560])).
% 12.93/5.12  tff(c_4627, plain, (![B_761]: (v1_xboole_0('#skF_1'('#skF_2', B_761)) | ~v1_xboole_0(k1_xboole_0) | ~v2_tex_2(B_761, '#skF_2') | ~m1_subset_1(B_761, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_4607, c_10])).
% 12.93/5.12  tff(c_4637, plain, (![B_762]: (v1_xboole_0('#skF_1'('#skF_2', B_762)) | ~v2_tex_2(B_762, '#skF_2') | ~m1_subset_1(B_762, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_4627])).
% 12.93/5.12  tff(c_4654, plain, (v1_xboole_0('#skF_1'('#skF_2', k1_xboole_0)) | ~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_6, c_4637])).
% 12.93/5.12  tff(c_4661, plain, (v1_xboole_0('#skF_1'('#skF_2', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2048, c_4654])).
% 12.93/5.12  tff(c_4665, plain, ('#skF_1'('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4661, c_2])).
% 12.93/5.12  tff(c_2073, plain, (![A_569, B_570]: (v3_tex_2('#skF_1'(A_569, B_570), A_569) | ~v2_tex_2(B_570, A_569) | ~m1_subset_1(B_570, k1_zfmisc_1(u1_struct_0(A_569))) | ~l1_pre_topc(A_569) | ~v3_tdlat_3(A_569) | ~v2_pre_topc(A_569) | v2_struct_0(A_569))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.93/5.12  tff(c_2079, plain, (![B_570]: (v3_tex_2('#skF_1'('#skF_2', B_570), '#skF_2') | ~v2_tex_2(B_570, '#skF_2') | ~m1_subset_1(B_570, k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1425, c_2073])).
% 12.93/5.12  tff(c_2091, plain, (![B_570]: (v3_tex_2('#skF_1'('#skF_2', B_570), '#skF_2') | ~v2_tex_2(B_570, '#skF_2') | ~m1_subset_1(B_570, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_2079])).
% 12.93/5.12  tff(c_2092, plain, (![B_570]: (v3_tex_2('#skF_1'('#skF_2', B_570), '#skF_2') | ~v2_tex_2(B_570, '#skF_2') | ~m1_subset_1(B_570, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_74, c_2091])).
% 12.93/5.12  tff(c_4677, plain, (v3_tex_2(k1_xboole_0, '#skF_2') | ~v2_tex_2(k1_xboole_0, '#skF_2') | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4665, c_2092])).
% 12.93/5.12  tff(c_4688, plain, (v3_tex_2(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2048, c_4677])).
% 12.93/5.12  tff(c_4690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1952, c_4688])).
% 12.93/5.12  tff(c_4691, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_1415])).
% 12.93/5.12  tff(c_4703, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4691, c_76])).
% 12.93/5.12  tff(c_17391, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7822, c_4703])).
% 12.93/5.12  tff(c_19447, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_19436, c_17391])).
% 12.93/5.12  tff(c_19451, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_19447])).
% 12.93/5.12  tff(c_19454, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_19451])).
% 12.93/5.12  tff(c_19456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7823, c_19454])).
% 12.93/5.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.93/5.12  
% 12.93/5.12  Inference rules
% 12.93/5.12  ----------------------
% 12.93/5.12  #Ref     : 0
% 12.93/5.12  #Sup     : 4022
% 12.93/5.12  #Fact    : 0
% 12.93/5.12  #Define  : 0
% 12.93/5.12  #Split   : 76
% 12.93/5.12  #Chain   : 0
% 12.93/5.12  #Close   : 0
% 12.93/5.12  
% 12.93/5.12  Ordering : KBO
% 12.93/5.12  
% 12.93/5.12  Simplification rules
% 12.93/5.12  ----------------------
% 12.93/5.12  #Subsume      : 1084
% 12.93/5.12  #Demod        : 3434
% 12.93/5.12  #Tautology    : 1242
% 12.93/5.12  #SimpNegUnit  : 687
% 12.93/5.12  #BackRed      : 294
% 12.93/5.12  
% 12.93/5.12  #Partial instantiations: 0
% 12.93/5.12  #Strategies tried      : 1
% 12.93/5.12  
% 12.93/5.12  Timing (in seconds)
% 12.93/5.12  ----------------------
% 12.93/5.12  Preprocessing        : 0.38
% 12.93/5.12  Parsing              : 0.21
% 12.93/5.12  CNF conversion       : 0.03
% 12.93/5.12  Main loop            : 3.94
% 12.93/5.12  Inferencing          : 1.41
% 12.93/5.12  Reduction            : 1.22
% 12.93/5.12  Demodulation         : 0.84
% 12.93/5.12  BG Simplification    : 0.10
% 12.93/5.12  Subsumption          : 0.95
% 12.93/5.12  Abstraction          : 0.13
% 12.93/5.12  MUC search           : 0.00
% 12.93/5.12  Cooper               : 0.00
% 12.93/5.12  Total                : 4.39
% 12.93/5.12  Index Insertion      : 0.00
% 12.93/5.12  Index Deletion       : 0.00
% 12.93/5.12  Index Matching       : 0.00
% 12.93/5.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
