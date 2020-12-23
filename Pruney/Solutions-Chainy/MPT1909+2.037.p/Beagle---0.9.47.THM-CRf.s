%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:42 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 196 expanded)
%              Number of leaves         :   47 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  261 ( 921 expanded)
%              Number of equality atoms :   24 ( 116 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_189,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_150,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_60,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_42,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_71,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_119,plain,(
    ! [A_134,B_135] :
      ( k6_domain_1(A_134,B_135) = k1_tarski(B_135)
      | ~ m1_subset_1(B_135,A_134)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_134,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_119])).

tff(c_136,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_26,plain,(
    ! [B_47,A_45] :
      ( m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_pre_topc(B_47,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_336,plain,(
    ! [B_206,A_207] :
      ( v3_tex_2(u1_struct_0(B_206),A_207)
      | ~ m1_subset_1(u1_struct_0(B_206),k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ v4_tex_2(B_206,A_207)
      | ~ m1_pre_topc(B_206,A_207)
      | ~ l1_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_341,plain,(
    ! [B_208,A_209] :
      ( v3_tex_2(u1_struct_0(B_208),A_209)
      | ~ v4_tex_2(B_208,A_209)
      | v2_struct_0(A_209)
      | ~ m1_pre_topc(B_208,A_209)
      | ~ l1_pre_topc(A_209) ) ),
    inference(resolution,[status(thm)],[c_26,c_336])).

tff(c_266,plain,(
    ! [B_182,A_183] :
      ( ~ v3_tex_2(B_182,A_183)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ v1_xboole_0(B_182)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_285,plain,(
    ! [B_47,A_45] :
      ( ~ v3_tex_2(u1_struct_0(B_47),A_45)
      | ~ v1_xboole_0(u1_struct_0(B_47))
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45)
      | ~ m1_pre_topc(B_47,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_26,c_266])).

tff(c_346,plain,(
    ! [B_210,A_211] :
      ( ~ v1_xboole_0(u1_struct_0(B_210))
      | ~ v2_pre_topc(A_211)
      | ~ v4_tex_2(B_210,A_211)
      | v2_struct_0(A_211)
      | ~ m1_pre_topc(B_210,A_211)
      | ~ l1_pre_topc(A_211) ) ),
    inference(resolution,[status(thm)],[c_341,c_285])).

tff(c_379,plain,(
    ! [A_217] :
      ( ~ v2_pre_topc(A_217)
      | ~ v4_tex_2('#skF_3',A_217)
      | v2_struct_0(A_217)
      | ~ m1_pre_topc('#skF_3',A_217)
      | ~ l1_pre_topc(A_217) ) ),
    inference(resolution,[status(thm)],[c_136,c_346])).

tff(c_386,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_379])).

tff(c_390,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_68,c_386])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_390])).

tff(c_394,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_18,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_52,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_48,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_16,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k1_tarski(A_29),k1_zfmisc_1(B_30))
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_504,plain,(
    ! [C_255,A_256,B_257] :
      ( m1_subset_1(C_255,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ m1_subset_1(C_255,k1_zfmisc_1(u1_struct_0(B_257)))
      | ~ m1_pre_topc(B_257,A_256)
      | ~ l1_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_523,plain,(
    ! [A_268,A_269,B_270] :
      ( m1_subset_1(k1_tarski(A_268),k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ m1_pre_topc(B_270,A_269)
      | ~ l1_pre_topc(A_269)
      | ~ r2_hidden(A_268,u1_struct_0(B_270)) ) ),
    inference(resolution,[status(thm)],[c_16,c_504])).

tff(c_525,plain,(
    ! [A_268] :
      ( m1_subset_1(k1_tarski(A_268),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_268,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_58,c_523])).

tff(c_528,plain,(
    ! [A_268] :
      ( m1_subset_1(k1_tarski(A_268),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_268,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_525])).

tff(c_641,plain,(
    ! [A_306,B_307,C_308,E_309] :
      ( k8_relset_1(u1_struct_0(A_306),u1_struct_0(B_307),C_308,E_309) = k2_pre_topc(A_306,E_309)
      | ~ m1_subset_1(E_309,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ m1_subset_1(E_309,k1_zfmisc_1(u1_struct_0(B_307)))
      | ~ v3_borsuk_1(C_308,A_306,B_307)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_306),u1_struct_0(B_307))))
      | ~ v5_pre_topc(C_308,A_306,B_307)
      | ~ v1_funct_2(C_308,u1_struct_0(A_306),u1_struct_0(B_307))
      | ~ v1_funct_1(C_308)
      | ~ m1_pre_topc(B_307,A_306)
      | ~ v4_tex_2(B_307,A_306)
      | v2_struct_0(B_307)
      | ~ l1_pre_topc(A_306)
      | ~ v3_tdlat_3(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_647,plain,(
    ! [B_307,C_308,A_268] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_307),C_308,k1_tarski(A_268)) = k2_pre_topc('#skF_2',k1_tarski(A_268))
      | ~ m1_subset_1(k1_tarski(A_268),k1_zfmisc_1(u1_struct_0(B_307)))
      | ~ v3_borsuk_1(C_308,'#skF_2',B_307)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_307))))
      | ~ v5_pre_topc(C_308,'#skF_2',B_307)
      | ~ v1_funct_2(C_308,u1_struct_0('#skF_2'),u1_struct_0(B_307))
      | ~ v1_funct_1(C_308)
      | ~ m1_pre_topc(B_307,'#skF_2')
      | ~ v4_tex_2(B_307,'#skF_2')
      | v2_struct_0(B_307)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_268,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_528,c_641])).

tff(c_657,plain,(
    ! [B_307,C_308,A_268] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_307),C_308,k1_tarski(A_268)) = k2_pre_topc('#skF_2',k1_tarski(A_268))
      | ~ m1_subset_1(k1_tarski(A_268),k1_zfmisc_1(u1_struct_0(B_307)))
      | ~ v3_borsuk_1(C_308,'#skF_2',B_307)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_307))))
      | ~ v5_pre_topc(C_308,'#skF_2',B_307)
      | ~ v1_funct_2(C_308,u1_struct_0('#skF_2'),u1_struct_0(B_307))
      | ~ v1_funct_1(C_308)
      | ~ m1_pre_topc(B_307,'#skF_2')
      | ~ v4_tex_2(B_307,'#skF_2')
      | v2_struct_0(B_307)
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_268,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_647])).

tff(c_668,plain,(
    ! [B_316,C_317,A_318] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_316),C_317,k1_tarski(A_318)) = k2_pre_topc('#skF_2',k1_tarski(A_318))
      | ~ m1_subset_1(k1_tarski(A_318),k1_zfmisc_1(u1_struct_0(B_316)))
      | ~ v3_borsuk_1(C_317,'#skF_2',B_316)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_316))))
      | ~ v5_pre_topc(C_317,'#skF_2',B_316)
      | ~ v1_funct_2(C_317,u1_struct_0('#skF_2'),u1_struct_0(B_316))
      | ~ v1_funct_1(C_317)
      | ~ m1_pre_topc(B_316,'#skF_2')
      | ~ v4_tex_2(B_316,'#skF_2')
      | v2_struct_0(B_316)
      | ~ r2_hidden(A_318,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_657])).

tff(c_768,plain,(
    ! [B_346,C_347,A_348] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_346),C_347,k1_tarski(A_348)) = k2_pre_topc('#skF_2',k1_tarski(A_348))
      | ~ v3_borsuk_1(C_347,'#skF_2',B_346)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_346))))
      | ~ v5_pre_topc(C_347,'#skF_2',B_346)
      | ~ v1_funct_2(C_347,u1_struct_0('#skF_2'),u1_struct_0(B_346))
      | ~ v1_funct_1(C_347)
      | ~ m1_pre_topc(B_346,'#skF_2')
      | ~ v4_tex_2(B_346,'#skF_2')
      | v2_struct_0(B_346)
      | ~ r2_hidden(A_348,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_348,u1_struct_0(B_346)) ) ),
    inference(resolution,[status(thm)],[c_16,c_668])).

tff(c_770,plain,(
    ! [A_348] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_348)) = k2_pre_topc('#skF_2',k1_tarski(A_348))
      | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ v4_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_348,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_50,c_768])).

tff(c_776,plain,(
    ! [A_348] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_348)) = k2_pre_topc('#skF_2',k1_tarski(A_348))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_348,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_48,c_770])).

tff(c_779,plain,(
    ! [A_349] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_349)) = k2_pre_topc('#skF_2',k1_tarski(A_349))
      | ~ r2_hidden(A_349,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_776])).

tff(c_393,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_135,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_119])).

tff(c_395,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_401,plain,(
    ! [B_218,A_219] :
      ( m1_subset_1(u1_struct_0(B_218),k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ m1_pre_topc(B_218,A_219)
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [C_35,B_34,A_33] :
      ( ~ v1_xboole_0(C_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_35))
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_418,plain,(
    ! [A_224,A_225,B_226] :
      ( ~ v1_xboole_0(u1_struct_0(A_224))
      | ~ r2_hidden(A_225,u1_struct_0(B_226))
      | ~ m1_pre_topc(B_226,A_224)
      | ~ l1_pre_topc(A_224) ) ),
    inference(resolution,[status(thm)],[c_401,c_20])).

tff(c_420,plain,(
    ! [A_225,B_226] :
      ( ~ r2_hidden(A_225,u1_struct_0(B_226))
      | ~ m1_pre_topc(B_226,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_395,c_418])).

tff(c_433,plain,(
    ! [A_232,B_233] :
      ( ~ r2_hidden(A_232,u1_struct_0(B_233))
      | ~ m1_pre_topc(B_233,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_420])).

tff(c_439,plain,(
    ! [B_234,A_235] :
      ( ~ m1_pre_topc(B_234,'#skF_2')
      | v1_xboole_0(u1_struct_0(B_234))
      | ~ m1_subset_1(A_235,u1_struct_0(B_234)) ) ),
    inference(resolution,[status(thm)],[c_18,c_433])).

tff(c_442,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_439])).

tff(c_448,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_442])).

tff(c_450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_448])).

tff(c_451,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_40,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_72,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_454,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_72])).

tff(c_503,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_454])).

tff(c_790,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_503])).

tff(c_798,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_790])).

tff(c_801,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_798])).

tff(c_803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:31:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.58  
% 3.54/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.58  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.54/1.58  
% 3.54/1.58  %Foreground sorts:
% 3.54/1.58  
% 3.54/1.58  
% 3.54/1.58  %Background operators:
% 3.54/1.58  
% 3.54/1.58  
% 3.54/1.58  %Foreground operators:
% 3.54/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.54/1.58  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.54/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.54/1.58  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.54/1.58  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.54/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.54/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.58  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.54/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.54/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.54/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.58  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.54/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.54/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.54/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.58  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.54/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.58  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.54/1.58  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.54/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.54/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.54/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.54/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.54/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.58  
% 3.54/1.60  tff(f_189, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 3.54/1.60  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.54/1.60  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.54/1.60  tff(f_97, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 3.54/1.60  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 3.54/1.60  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.54/1.60  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.54/1.60  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 3.54/1.60  tff(f_150, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 3.54/1.60  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.54/1.60  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_60, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_42, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_71, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 3.54/1.60  tff(c_119, plain, (![A_134, B_135]: (k6_domain_1(A_134, B_135)=k1_tarski(B_135) | ~m1_subset_1(B_135, A_134) | v1_xboole_0(A_134))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.54/1.60  tff(c_134, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_119])).
% 3.54/1.60  tff(c_136, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_134])).
% 3.54/1.60  tff(c_26, plain, (![B_47, A_45]: (m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_pre_topc(B_47, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.54/1.60  tff(c_336, plain, (![B_206, A_207]: (v3_tex_2(u1_struct_0(B_206), A_207) | ~m1_subset_1(u1_struct_0(B_206), k1_zfmisc_1(u1_struct_0(A_207))) | ~v4_tex_2(B_206, A_207) | ~m1_pre_topc(B_206, A_207) | ~l1_pre_topc(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.54/1.60  tff(c_341, plain, (![B_208, A_209]: (v3_tex_2(u1_struct_0(B_208), A_209) | ~v4_tex_2(B_208, A_209) | v2_struct_0(A_209) | ~m1_pre_topc(B_208, A_209) | ~l1_pre_topc(A_209))), inference(resolution, [status(thm)], [c_26, c_336])).
% 3.54/1.60  tff(c_266, plain, (![B_182, A_183]: (~v3_tex_2(B_182, A_183) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_183))) | ~v1_xboole_0(B_182) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.54/1.60  tff(c_285, plain, (![B_47, A_45]: (~v3_tex_2(u1_struct_0(B_47), A_45) | ~v1_xboole_0(u1_struct_0(B_47)) | ~v2_pre_topc(A_45) | v2_struct_0(A_45) | ~m1_pre_topc(B_47, A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_26, c_266])).
% 3.54/1.60  tff(c_346, plain, (![B_210, A_211]: (~v1_xboole_0(u1_struct_0(B_210)) | ~v2_pre_topc(A_211) | ~v4_tex_2(B_210, A_211) | v2_struct_0(A_211) | ~m1_pre_topc(B_210, A_211) | ~l1_pre_topc(A_211))), inference(resolution, [status(thm)], [c_341, c_285])).
% 3.54/1.60  tff(c_379, plain, (![A_217]: (~v2_pre_topc(A_217) | ~v4_tex_2('#skF_3', A_217) | v2_struct_0(A_217) | ~m1_pre_topc('#skF_3', A_217) | ~l1_pre_topc(A_217))), inference(resolution, [status(thm)], [c_136, c_346])).
% 3.54/1.60  tff(c_386, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_379])).
% 3.54/1.60  tff(c_390, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_68, c_386])).
% 3.54/1.60  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_390])).
% 3.54/1.60  tff(c_394, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_134])).
% 3.54/1.60  tff(c_18, plain, (![A_31, B_32]: (r2_hidden(A_31, B_32) | v1_xboole_0(B_32) | ~m1_subset_1(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.54/1.60  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_54, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_52, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_48, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_16, plain, (![A_29, B_30]: (m1_subset_1(k1_tarski(A_29), k1_zfmisc_1(B_30)) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.60  tff(c_66, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_504, plain, (![C_255, A_256, B_257]: (m1_subset_1(C_255, k1_zfmisc_1(u1_struct_0(A_256))) | ~m1_subset_1(C_255, k1_zfmisc_1(u1_struct_0(B_257))) | ~m1_pre_topc(B_257, A_256) | ~l1_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.54/1.60  tff(c_523, plain, (![A_268, A_269, B_270]: (m1_subset_1(k1_tarski(A_268), k1_zfmisc_1(u1_struct_0(A_269))) | ~m1_pre_topc(B_270, A_269) | ~l1_pre_topc(A_269) | ~r2_hidden(A_268, u1_struct_0(B_270)))), inference(resolution, [status(thm)], [c_16, c_504])).
% 3.54/1.60  tff(c_525, plain, (![A_268]: (m1_subset_1(k1_tarski(A_268), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_268, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_58, c_523])).
% 3.54/1.60  tff(c_528, plain, (![A_268]: (m1_subset_1(k1_tarski(A_268), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_268, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_525])).
% 3.54/1.60  tff(c_641, plain, (![A_306, B_307, C_308, E_309]: (k8_relset_1(u1_struct_0(A_306), u1_struct_0(B_307), C_308, E_309)=k2_pre_topc(A_306, E_309) | ~m1_subset_1(E_309, k1_zfmisc_1(u1_struct_0(A_306))) | ~m1_subset_1(E_309, k1_zfmisc_1(u1_struct_0(B_307))) | ~v3_borsuk_1(C_308, A_306, B_307) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_306), u1_struct_0(B_307)))) | ~v5_pre_topc(C_308, A_306, B_307) | ~v1_funct_2(C_308, u1_struct_0(A_306), u1_struct_0(B_307)) | ~v1_funct_1(C_308) | ~m1_pre_topc(B_307, A_306) | ~v4_tex_2(B_307, A_306) | v2_struct_0(B_307) | ~l1_pre_topc(A_306) | ~v3_tdlat_3(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.54/1.60  tff(c_647, plain, (![B_307, C_308, A_268]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_307), C_308, k1_tarski(A_268))=k2_pre_topc('#skF_2', k1_tarski(A_268)) | ~m1_subset_1(k1_tarski(A_268), k1_zfmisc_1(u1_struct_0(B_307))) | ~v3_borsuk_1(C_308, '#skF_2', B_307) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_307)))) | ~v5_pre_topc(C_308, '#skF_2', B_307) | ~v1_funct_2(C_308, u1_struct_0('#skF_2'), u1_struct_0(B_307)) | ~v1_funct_1(C_308) | ~m1_pre_topc(B_307, '#skF_2') | ~v4_tex_2(B_307, '#skF_2') | v2_struct_0(B_307) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(A_268, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_528, c_641])).
% 3.54/1.60  tff(c_657, plain, (![B_307, C_308, A_268]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_307), C_308, k1_tarski(A_268))=k2_pre_topc('#skF_2', k1_tarski(A_268)) | ~m1_subset_1(k1_tarski(A_268), k1_zfmisc_1(u1_struct_0(B_307))) | ~v3_borsuk_1(C_308, '#skF_2', B_307) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_307)))) | ~v5_pre_topc(C_308, '#skF_2', B_307) | ~v1_funct_2(C_308, u1_struct_0('#skF_2'), u1_struct_0(B_307)) | ~v1_funct_1(C_308) | ~m1_pre_topc(B_307, '#skF_2') | ~v4_tex_2(B_307, '#skF_2') | v2_struct_0(B_307) | v2_struct_0('#skF_2') | ~r2_hidden(A_268, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_647])).
% 3.54/1.60  tff(c_668, plain, (![B_316, C_317, A_318]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_316), C_317, k1_tarski(A_318))=k2_pre_topc('#skF_2', k1_tarski(A_318)) | ~m1_subset_1(k1_tarski(A_318), k1_zfmisc_1(u1_struct_0(B_316))) | ~v3_borsuk_1(C_317, '#skF_2', B_316) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_316)))) | ~v5_pre_topc(C_317, '#skF_2', B_316) | ~v1_funct_2(C_317, u1_struct_0('#skF_2'), u1_struct_0(B_316)) | ~v1_funct_1(C_317) | ~m1_pre_topc(B_316, '#skF_2') | ~v4_tex_2(B_316, '#skF_2') | v2_struct_0(B_316) | ~r2_hidden(A_318, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_70, c_657])).
% 3.54/1.60  tff(c_768, plain, (![B_346, C_347, A_348]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_346), C_347, k1_tarski(A_348))=k2_pre_topc('#skF_2', k1_tarski(A_348)) | ~v3_borsuk_1(C_347, '#skF_2', B_346) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_346)))) | ~v5_pre_topc(C_347, '#skF_2', B_346) | ~v1_funct_2(C_347, u1_struct_0('#skF_2'), u1_struct_0(B_346)) | ~v1_funct_1(C_347) | ~m1_pre_topc(B_346, '#skF_2') | ~v4_tex_2(B_346, '#skF_2') | v2_struct_0(B_346) | ~r2_hidden(A_348, u1_struct_0('#skF_3')) | ~r2_hidden(A_348, u1_struct_0(B_346)))), inference(resolution, [status(thm)], [c_16, c_668])).
% 3.54/1.60  tff(c_770, plain, (![A_348]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_348))=k2_pre_topc('#skF_2', k1_tarski(A_348)) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~r2_hidden(A_348, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_50, c_768])).
% 3.54/1.60  tff(c_776, plain, (![A_348]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_348))=k2_pre_topc('#skF_2', k1_tarski(A_348)) | v2_struct_0('#skF_3') | ~r2_hidden(A_348, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_48, c_770])).
% 3.54/1.60  tff(c_779, plain, (![A_349]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_349))=k2_pre_topc('#skF_2', k1_tarski(A_349)) | ~r2_hidden(A_349, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_776])).
% 3.54/1.60  tff(c_393, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_134])).
% 3.54/1.60  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_135, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_119])).
% 3.54/1.60  tff(c_395, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_135])).
% 3.54/1.60  tff(c_401, plain, (![B_218, A_219]: (m1_subset_1(u1_struct_0(B_218), k1_zfmisc_1(u1_struct_0(A_219))) | ~m1_pre_topc(B_218, A_219) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.54/1.60  tff(c_20, plain, (![C_35, B_34, A_33]: (~v1_xboole_0(C_35) | ~m1_subset_1(B_34, k1_zfmisc_1(C_35)) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.54/1.60  tff(c_418, plain, (![A_224, A_225, B_226]: (~v1_xboole_0(u1_struct_0(A_224)) | ~r2_hidden(A_225, u1_struct_0(B_226)) | ~m1_pre_topc(B_226, A_224) | ~l1_pre_topc(A_224))), inference(resolution, [status(thm)], [c_401, c_20])).
% 3.54/1.60  tff(c_420, plain, (![A_225, B_226]: (~r2_hidden(A_225, u1_struct_0(B_226)) | ~m1_pre_topc(B_226, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_395, c_418])).
% 3.54/1.60  tff(c_433, plain, (![A_232, B_233]: (~r2_hidden(A_232, u1_struct_0(B_233)) | ~m1_pre_topc(B_233, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_420])).
% 3.54/1.60  tff(c_439, plain, (![B_234, A_235]: (~m1_pre_topc(B_234, '#skF_2') | v1_xboole_0(u1_struct_0(B_234)) | ~m1_subset_1(A_235, u1_struct_0(B_234)))), inference(resolution, [status(thm)], [c_18, c_433])).
% 3.54/1.60  tff(c_442, plain, (~m1_pre_topc('#skF_3', '#skF_2') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_439])).
% 3.54/1.60  tff(c_448, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_442])).
% 3.54/1.60  tff(c_450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_394, c_448])).
% 3.54/1.60  tff(c_451, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_135])).
% 3.54/1.60  tff(c_40, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.54/1.60  tff(c_72, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 3.54/1.60  tff(c_454, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_451, c_72])).
% 3.54/1.60  tff(c_503, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_454])).
% 3.54/1.60  tff(c_790, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_779, c_503])).
% 3.54/1.60  tff(c_798, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_790])).
% 3.54/1.60  tff(c_801, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_798])).
% 3.54/1.60  tff(c_803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_394, c_801])).
% 3.54/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.60  
% 3.54/1.60  Inference rules
% 3.54/1.60  ----------------------
% 3.54/1.60  #Ref     : 0
% 3.54/1.60  #Sup     : 155
% 3.54/1.60  #Fact    : 0
% 3.54/1.60  #Define  : 0
% 3.54/1.60  #Split   : 13
% 3.54/1.60  #Chain   : 0
% 3.54/1.60  #Close   : 0
% 3.54/1.60  
% 3.54/1.60  Ordering : KBO
% 3.54/1.60  
% 3.54/1.60  Simplification rules
% 3.54/1.60  ----------------------
% 3.54/1.60  #Subsume      : 9
% 3.54/1.60  #Demod        : 40
% 3.54/1.60  #Tautology    : 59
% 3.54/1.60  #SimpNegUnit  : 11
% 3.54/1.60  #BackRed      : 2
% 3.54/1.60  
% 3.54/1.60  #Partial instantiations: 0
% 3.54/1.60  #Strategies tried      : 1
% 3.54/1.60  
% 3.54/1.60  Timing (in seconds)
% 3.54/1.60  ----------------------
% 3.54/1.60  Preprocessing        : 0.38
% 3.54/1.60  Parsing              : 0.20
% 3.54/1.60  CNF conversion       : 0.03
% 3.54/1.60  Main loop            : 0.44
% 3.54/1.60  Inferencing          : 0.17
% 3.54/1.60  Reduction            : 0.13
% 3.54/1.60  Demodulation         : 0.09
% 3.54/1.60  BG Simplification    : 0.03
% 3.54/1.60  Subsumption          : 0.08
% 3.54/1.60  Abstraction          : 0.02
% 3.54/1.60  MUC search           : 0.00
% 3.54/1.60  Cooper               : 0.00
% 3.54/1.60  Total                : 0.87
% 3.54/1.60  Index Insertion      : 0.00
% 3.54/1.60  Index Deletion       : 0.00
% 3.54/1.61  Index Matching       : 0.00
% 3.54/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
