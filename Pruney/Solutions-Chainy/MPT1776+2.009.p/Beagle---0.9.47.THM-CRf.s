%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:30 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 371 expanded)
%              Number of leaves         :   34 ( 160 expanded)
%              Depth                    :   13
%              Number of atoms          :  465 (3081 expanded)
%              Number of equality atoms :   31 ( 153 expanded)
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

tff(f_238,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_32,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_75,plain,(
    ! [B_253,A_254] :
      ( l1_pre_topc(B_253)
      | ~ m1_pre_topc(B_253,A_254)
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_87,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_78])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_14,plain,(
    ! [B_62,A_60] :
      ( r1_tarski(u1_struct_0(B_62),u1_struct_0(A_60))
      | ~ m1_pre_topc(B_62,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_361,plain,(
    ! [B_306,C_307,A_308] :
      ( v1_tsep_1(B_306,C_307)
      | ~ r1_tarski(u1_struct_0(B_306),u1_struct_0(C_307))
      | ~ m1_pre_topc(C_307,A_308)
      | v2_struct_0(C_307)
      | ~ m1_pre_topc(B_306,A_308)
      | ~ v1_tsep_1(B_306,A_308)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_390,plain,(
    ! [B_314,A_315,A_316] :
      ( v1_tsep_1(B_314,A_315)
      | ~ m1_pre_topc(A_315,A_316)
      | v2_struct_0(A_315)
      | ~ m1_pre_topc(B_314,A_316)
      | ~ v1_tsep_1(B_314,A_316)
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316)
      | ~ m1_pre_topc(B_314,A_315)
      | ~ l1_pre_topc(A_315) ) ),
    inference(resolution,[status(thm)],[c_14,c_361])).

tff(c_394,plain,(
    ! [B_314] :
      ( v1_tsep_1(B_314,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_314,'#skF_2')
      | ~ v1_tsep_1(B_314,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_314,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_390])).

tff(c_405,plain,(
    ! [B_314] :
      ( v1_tsep_1(B_314,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_314,'#skF_2')
      | ~ v1_tsep_1(B_314,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_314,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_50,c_48,c_394])).

tff(c_415,plain,(
    ! [B_317] :
      ( v1_tsep_1(B_317,'#skF_4')
      | ~ m1_pre_topc(B_317,'#skF_2')
      | ~ v1_tsep_1(B_317,'#skF_2')
      | ~ m1_pre_topc(B_317,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_405])).

tff(c_418,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_415])).

tff(c_421,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_44,c_418])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_22,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_66,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_66])).

tff(c_142,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_60,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_69,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60])).

tff(c_144,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_69])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_94,plain,(
    ! [B_255,A_256] :
      ( v2_pre_topc(B_255)
      | ~ m1_pre_topc(B_255,A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_94])).

tff(c_106,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_97])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_166,plain,(
    ! [B_267,C_268,A_269] :
      ( v1_tsep_1(B_267,C_268)
      | ~ r1_tarski(u1_struct_0(B_267),u1_struct_0(C_268))
      | ~ m1_pre_topc(C_268,A_269)
      | v2_struct_0(C_268)
      | ~ m1_pre_topc(B_267,A_269)
      | ~ v1_tsep_1(B_267,A_269)
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_174,plain,(
    ! [B_273,A_274,A_275] :
      ( v1_tsep_1(B_273,A_274)
      | ~ m1_pre_topc(A_274,A_275)
      | v2_struct_0(A_274)
      | ~ m1_pre_topc(B_273,A_275)
      | ~ v1_tsep_1(B_273,A_275)
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275)
      | ~ m1_pre_topc(B_273,A_274)
      | ~ l1_pre_topc(A_274) ) ),
    inference(resolution,[status(thm)],[c_14,c_166])).

tff(c_178,plain,(
    ! [B_273] :
      ( v1_tsep_1(B_273,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_273,'#skF_2')
      | ~ v1_tsep_1(B_273,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_273,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_174])).

tff(c_189,plain,(
    ! [B_273] :
      ( v1_tsep_1(B_273,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_273,'#skF_2')
      | ~ v1_tsep_1(B_273,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_273,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_50,c_48,c_178])).

tff(c_199,plain,(
    ! [B_276] :
      ( v1_tsep_1(B_276,'#skF_4')
      | ~ m1_pre_topc(B_276,'#skF_2')
      | ~ v1_tsep_1(B_276,'#skF_2')
      | ~ m1_pre_topc(B_276,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_189])).

tff(c_202,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_199])).

tff(c_205,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_44,c_202])).

tff(c_256,plain,(
    ! [C_290,E_289,A_287,B_288,D_286] :
      ( k3_tmap_1(A_287,B_288,C_290,D_286,E_289) = k2_partfun1(u1_struct_0(C_290),u1_struct_0(B_288),E_289,u1_struct_0(D_286))
      | ~ m1_pre_topc(D_286,C_290)
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_290),u1_struct_0(B_288))))
      | ~ v1_funct_2(E_289,u1_struct_0(C_290),u1_struct_0(B_288))
      | ~ v1_funct_1(E_289)
      | ~ m1_pre_topc(D_286,A_287)
      | ~ m1_pre_topc(C_290,A_287)
      | ~ l1_pre_topc(B_288)
      | ~ v2_pre_topc(B_288)
      | v2_struct_0(B_288)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_258,plain,(
    ! [A_287,D_286] :
      ( k3_tmap_1(A_287,'#skF_1','#skF_4',D_286,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_286))
      | ~ m1_pre_topc(D_286,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_286,A_287)
      | ~ m1_pre_topc('#skF_4',A_287)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(resolution,[status(thm)],[c_34,c_256])).

tff(c_261,plain,(
    ! [A_287,D_286] :
      ( k3_tmap_1(A_287,'#skF_1','#skF_4',D_286,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_286))
      | ~ m1_pre_topc(D_286,'#skF_4')
      | ~ m1_pre_topc(D_286,A_287)
      | ~ m1_pre_topc('#skF_4',A_287)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_258])).

tff(c_263,plain,(
    ! [A_291,D_292] :
      ( k3_tmap_1(A_291,'#skF_1','#skF_4',D_292,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_292))
      | ~ m1_pre_topc(D_292,'#skF_4')
      | ~ m1_pre_topc(D_292,A_291)
      | ~ m1_pre_topc('#skF_4',A_291)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_261])).

tff(c_269,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_263])).

tff(c_281,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_28,c_269])).

tff(c_282,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_281])).

tff(c_221,plain,(
    ! [A_279,B_280,C_281,D_282] :
      ( k2_partfun1(u1_struct_0(A_279),u1_struct_0(B_280),C_281,u1_struct_0(D_282)) = k2_tmap_1(A_279,B_280,C_281,D_282)
      | ~ m1_pre_topc(D_282,A_279)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_279),u1_struct_0(B_280))))
      | ~ v1_funct_2(C_281,u1_struct_0(A_279),u1_struct_0(B_280))
      | ~ v1_funct_1(C_281)
      | ~ l1_pre_topc(B_280)
      | ~ v2_pre_topc(B_280)
      | v2_struct_0(B_280)
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,(
    ! [D_282] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_282)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_282)
      | ~ m1_pre_topc(D_282,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_221])).

tff(c_226,plain,(
    ! [D_282] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_282)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_282)
      | ~ m1_pre_topc(D_282,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_87,c_56,c_54,c_38,c_36,c_223])).

tff(c_227,plain,(
    ! [D_282] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_282)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_282)
      | ~ m1_pre_topc(D_282,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_58,c_226])).

tff(c_290,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_227])).

tff(c_297,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_290])).

tff(c_302,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_142])).

tff(c_343,plain,(
    ! [D_301,C_305,A_304,F_302,B_303] :
      ( r1_tmap_1(B_303,A_304,C_305,F_302)
      | ~ r1_tmap_1(D_301,A_304,k2_tmap_1(B_303,A_304,C_305,D_301),F_302)
      | ~ m1_subset_1(F_302,u1_struct_0(D_301))
      | ~ m1_subset_1(F_302,u1_struct_0(B_303))
      | ~ m1_pre_topc(D_301,B_303)
      | ~ v1_tsep_1(D_301,B_303)
      | v2_struct_0(D_301)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_303),u1_struct_0(A_304))))
      | ~ v1_funct_2(C_305,u1_struct_0(B_303),u1_struct_0(A_304))
      | ~ v1_funct_1(C_305)
      | ~ l1_pre_topc(B_303)
      | ~ v2_pre_topc(B_303)
      | v2_struct_0(B_303)
      | ~ l1_pre_topc(A_304)
      | ~ v2_pre_topc(A_304)
      | v2_struct_0(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_347,plain,
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
    inference(resolution,[status(thm)],[c_302,c_343])).

tff(c_354,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_106,c_87,c_38,c_36,c_34,c_205,c_28,c_26,c_70,c_347])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_42,c_46,c_144,c_354])).

tff(c_357,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_524,plain,(
    ! [A_337,C_338,B_336,F_335,D_334] :
      ( r1_tmap_1(D_334,A_337,k2_tmap_1(B_336,A_337,C_338,D_334),F_335)
      | ~ r1_tmap_1(B_336,A_337,C_338,F_335)
      | ~ m1_subset_1(F_335,u1_struct_0(D_334))
      | ~ m1_subset_1(F_335,u1_struct_0(B_336))
      | ~ m1_pre_topc(D_334,B_336)
      | ~ v1_tsep_1(D_334,B_336)
      | v2_struct_0(D_334)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_336),u1_struct_0(A_337))))
      | ~ v1_funct_2(C_338,u1_struct_0(B_336),u1_struct_0(A_337))
      | ~ v1_funct_1(C_338)
      | ~ l1_pre_topc(B_336)
      | ~ v2_pre_topc(B_336)
      | v2_struct_0(B_336)
      | ~ l1_pre_topc(A_337)
      | ~ v2_pre_topc(A_337)
      | v2_struct_0(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_526,plain,(
    ! [D_334,F_335] :
      ( r1_tmap_1(D_334,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_334),F_335)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_335)
      | ~ m1_subset_1(F_335,u1_struct_0(D_334))
      | ~ m1_subset_1(F_335,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_334,'#skF_4')
      | ~ v1_tsep_1(D_334,'#skF_4')
      | v2_struct_0(D_334)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_524])).

tff(c_529,plain,(
    ! [D_334,F_335] :
      ( r1_tmap_1(D_334,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_334),F_335)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_335)
      | ~ m1_subset_1(F_335,u1_struct_0(D_334))
      | ~ m1_subset_1(F_335,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_334,'#skF_4')
      | ~ v1_tsep_1(D_334,'#skF_4')
      | v2_struct_0(D_334)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_106,c_87,c_38,c_36,c_526])).

tff(c_558,plain,(
    ! [D_340,F_341] :
      ( r1_tmap_1(D_340,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_340),F_341)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_341)
      | ~ m1_subset_1(F_341,u1_struct_0(D_340))
      | ~ m1_subset_1(F_341,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_340,'#skF_4')
      | ~ v1_tsep_1(D_340,'#skF_4')
      | v2_struct_0(D_340) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_42,c_529])).

tff(c_472,plain,(
    ! [C_331,D_327,E_330,A_328,B_329] :
      ( k3_tmap_1(A_328,B_329,C_331,D_327,E_330) = k2_partfun1(u1_struct_0(C_331),u1_struct_0(B_329),E_330,u1_struct_0(D_327))
      | ~ m1_pre_topc(D_327,C_331)
      | ~ m1_subset_1(E_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_331),u1_struct_0(B_329))))
      | ~ v1_funct_2(E_330,u1_struct_0(C_331),u1_struct_0(B_329))
      | ~ v1_funct_1(E_330)
      | ~ m1_pre_topc(D_327,A_328)
      | ~ m1_pre_topc(C_331,A_328)
      | ~ l1_pre_topc(B_329)
      | ~ v2_pre_topc(B_329)
      | v2_struct_0(B_329)
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_474,plain,(
    ! [A_328,D_327] :
      ( k3_tmap_1(A_328,'#skF_1','#skF_4',D_327,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_327))
      | ~ m1_pre_topc(D_327,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_327,A_328)
      | ~ m1_pre_topc('#skF_4',A_328)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_34,c_472])).

tff(c_477,plain,(
    ! [A_328,D_327] :
      ( k3_tmap_1(A_328,'#skF_1','#skF_4',D_327,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_327))
      | ~ m1_pre_topc(D_327,'#skF_4')
      | ~ m1_pre_topc(D_327,A_328)
      | ~ m1_pre_topc('#skF_4',A_328)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_474])).

tff(c_479,plain,(
    ! [A_332,D_333] :
      ( k3_tmap_1(A_332,'#skF_1','#skF_4',D_333,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_333))
      | ~ m1_pre_topc(D_333,'#skF_4')
      | ~ m1_pre_topc(D_333,A_332)
      | ~ m1_pre_topc('#skF_4',A_332)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_477])).

tff(c_485,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_479])).

tff(c_497,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_28,c_485])).

tff(c_498,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_497])).

tff(c_436,plain,(
    ! [A_319,B_320,C_321,D_322] :
      ( k2_partfun1(u1_struct_0(A_319),u1_struct_0(B_320),C_321,u1_struct_0(D_322)) = k2_tmap_1(A_319,B_320,C_321,D_322)
      | ~ m1_pre_topc(D_322,A_319)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_319),u1_struct_0(B_320))))
      | ~ v1_funct_2(C_321,u1_struct_0(A_319),u1_struct_0(B_320))
      | ~ v1_funct_1(C_321)
      | ~ l1_pre_topc(B_320)
      | ~ v2_pre_topc(B_320)
      | v2_struct_0(B_320)
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_438,plain,(
    ! [D_322] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_322)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_322)
      | ~ m1_pre_topc(D_322,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_436])).

tff(c_441,plain,(
    ! [D_322] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_322)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_322)
      | ~ m1_pre_topc(D_322,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_87,c_56,c_54,c_38,c_36,c_438])).

tff(c_442,plain,(
    ! [D_322] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_322)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_322)
      | ~ m1_pre_topc(D_322,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_58,c_441])).

tff(c_506,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_442])).

tff(c_513,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_506])).

tff(c_358,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_518,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_358])).

tff(c_561,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_558,c_518])).

tff(c_564,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_28,c_26,c_70,c_357,c_561])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.50  
% 3.21/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.51  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.21/1.51  
% 3.21/1.51  %Foreground sorts:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Background operators:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Foreground operators:
% 3.21/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.51  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.51  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.21/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.21/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.21/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.21/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.21/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.51  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.21/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.21/1.51  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.21/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.51  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.21/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.51  
% 3.21/1.53  tff(f_238, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tmap_1)).
% 3.21/1.53  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.21/1.53  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.21/1.53  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tsep_1)).
% 3.21/1.53  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.21/1.53  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.21/1.53  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.21/1.53  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.21/1.53  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_32, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_75, plain, (![B_253, A_254]: (l1_pre_topc(B_253) | ~m1_pre_topc(B_253, A_254) | ~l1_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.21/1.53  tff(c_78, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_75])).
% 3.21/1.53  tff(c_87, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_78])).
% 3.21/1.53  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_14, plain, (![B_62, A_60]: (r1_tarski(u1_struct_0(B_62), u1_struct_0(A_60)) | ~m1_pre_topc(B_62, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.21/1.53  tff(c_361, plain, (![B_306, C_307, A_308]: (v1_tsep_1(B_306, C_307) | ~r1_tarski(u1_struct_0(B_306), u1_struct_0(C_307)) | ~m1_pre_topc(C_307, A_308) | v2_struct_0(C_307) | ~m1_pre_topc(B_306, A_308) | ~v1_tsep_1(B_306, A_308) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.21/1.53  tff(c_390, plain, (![B_314, A_315, A_316]: (v1_tsep_1(B_314, A_315) | ~m1_pre_topc(A_315, A_316) | v2_struct_0(A_315) | ~m1_pre_topc(B_314, A_316) | ~v1_tsep_1(B_314, A_316) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316) | v2_struct_0(A_316) | ~m1_pre_topc(B_314, A_315) | ~l1_pre_topc(A_315))), inference(resolution, [status(thm)], [c_14, c_361])).
% 3.21/1.53  tff(c_394, plain, (![B_314]: (v1_tsep_1(B_314, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_314, '#skF_2') | ~v1_tsep_1(B_314, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_314, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_390])).
% 3.21/1.53  tff(c_405, plain, (![B_314]: (v1_tsep_1(B_314, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_314, '#skF_2') | ~v1_tsep_1(B_314, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_314, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_50, c_48, c_394])).
% 3.21/1.53  tff(c_415, plain, (![B_317]: (v1_tsep_1(B_317, '#skF_4') | ~m1_pre_topc(B_317, '#skF_2') | ~v1_tsep_1(B_317, '#skF_2') | ~m1_pre_topc(B_317, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_405])).
% 3.21/1.53  tff(c_418, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_415])).
% 3.21/1.53  tff(c_421, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_44, c_418])).
% 3.21/1.53  tff(c_26, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_22, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_24, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 3.21/1.53  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_66, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_68, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_66])).
% 3.21/1.53  tff(c_142, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_68])).
% 3.21/1.53  tff(c_60, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_69, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_60])).
% 3.21/1.53  tff(c_144, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_69])).
% 3.21/1.53  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_94, plain, (![B_255, A_256]: (v2_pre_topc(B_255) | ~m1_pre_topc(B_255, A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.21/1.53  tff(c_97, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_94])).
% 3.21/1.53  tff(c_106, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_97])).
% 3.21/1.53  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_36, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.21/1.53  tff(c_166, plain, (![B_267, C_268, A_269]: (v1_tsep_1(B_267, C_268) | ~r1_tarski(u1_struct_0(B_267), u1_struct_0(C_268)) | ~m1_pre_topc(C_268, A_269) | v2_struct_0(C_268) | ~m1_pre_topc(B_267, A_269) | ~v1_tsep_1(B_267, A_269) | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.21/1.53  tff(c_174, plain, (![B_273, A_274, A_275]: (v1_tsep_1(B_273, A_274) | ~m1_pre_topc(A_274, A_275) | v2_struct_0(A_274) | ~m1_pre_topc(B_273, A_275) | ~v1_tsep_1(B_273, A_275) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275) | v2_struct_0(A_275) | ~m1_pre_topc(B_273, A_274) | ~l1_pre_topc(A_274))), inference(resolution, [status(thm)], [c_14, c_166])).
% 3.21/1.53  tff(c_178, plain, (![B_273]: (v1_tsep_1(B_273, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_273, '#skF_2') | ~v1_tsep_1(B_273, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_273, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_174])).
% 3.21/1.53  tff(c_189, plain, (![B_273]: (v1_tsep_1(B_273, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_273, '#skF_2') | ~v1_tsep_1(B_273, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_273, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_50, c_48, c_178])).
% 3.21/1.53  tff(c_199, plain, (![B_276]: (v1_tsep_1(B_276, '#skF_4') | ~m1_pre_topc(B_276, '#skF_2') | ~v1_tsep_1(B_276, '#skF_2') | ~m1_pre_topc(B_276, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_189])).
% 3.21/1.53  tff(c_202, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_199])).
% 3.21/1.53  tff(c_205, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_44, c_202])).
% 3.21/1.53  tff(c_256, plain, (![C_290, E_289, A_287, B_288, D_286]: (k3_tmap_1(A_287, B_288, C_290, D_286, E_289)=k2_partfun1(u1_struct_0(C_290), u1_struct_0(B_288), E_289, u1_struct_0(D_286)) | ~m1_pre_topc(D_286, C_290) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_290), u1_struct_0(B_288)))) | ~v1_funct_2(E_289, u1_struct_0(C_290), u1_struct_0(B_288)) | ~v1_funct_1(E_289) | ~m1_pre_topc(D_286, A_287) | ~m1_pre_topc(C_290, A_287) | ~l1_pre_topc(B_288) | ~v2_pre_topc(B_288) | v2_struct_0(B_288) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.53  tff(c_258, plain, (![A_287, D_286]: (k3_tmap_1(A_287, '#skF_1', '#skF_4', D_286, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_286)) | ~m1_pre_topc(D_286, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_286, A_287) | ~m1_pre_topc('#skF_4', A_287) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(resolution, [status(thm)], [c_34, c_256])).
% 3.21/1.53  tff(c_261, plain, (![A_287, D_286]: (k3_tmap_1(A_287, '#skF_1', '#skF_4', D_286, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_286)) | ~m1_pre_topc(D_286, '#skF_4') | ~m1_pre_topc(D_286, A_287) | ~m1_pre_topc('#skF_4', A_287) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_38, c_36, c_258])).
% 3.21/1.53  tff(c_263, plain, (![A_291, D_292]: (k3_tmap_1(A_291, '#skF_1', '#skF_4', D_292, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_292)) | ~m1_pre_topc(D_292, '#skF_4') | ~m1_pre_topc(D_292, A_291) | ~m1_pre_topc('#skF_4', A_291) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(negUnitSimplification, [status(thm)], [c_58, c_261])).
% 3.21/1.53  tff(c_269, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_263])).
% 3.21/1.53  tff(c_281, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_28, c_269])).
% 3.21/1.53  tff(c_282, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_281])).
% 3.21/1.53  tff(c_221, plain, (![A_279, B_280, C_281, D_282]: (k2_partfun1(u1_struct_0(A_279), u1_struct_0(B_280), C_281, u1_struct_0(D_282))=k2_tmap_1(A_279, B_280, C_281, D_282) | ~m1_pre_topc(D_282, A_279) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_279), u1_struct_0(B_280)))) | ~v1_funct_2(C_281, u1_struct_0(A_279), u1_struct_0(B_280)) | ~v1_funct_1(C_281) | ~l1_pre_topc(B_280) | ~v2_pre_topc(B_280) | v2_struct_0(B_280) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.53  tff(c_223, plain, (![D_282]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_282))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_282) | ~m1_pre_topc(D_282, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_221])).
% 3.21/1.53  tff(c_226, plain, (![D_282]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_282))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_282) | ~m1_pre_topc(D_282, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_87, c_56, c_54, c_38, c_36, c_223])).
% 3.21/1.53  tff(c_227, plain, (![D_282]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_282))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_282) | ~m1_pre_topc(D_282, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_58, c_226])).
% 3.21/1.53  tff(c_290, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_282, c_227])).
% 3.21/1.53  tff(c_297, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_290])).
% 3.21/1.53  tff(c_302, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_142])).
% 3.21/1.53  tff(c_343, plain, (![D_301, C_305, A_304, F_302, B_303]: (r1_tmap_1(B_303, A_304, C_305, F_302) | ~r1_tmap_1(D_301, A_304, k2_tmap_1(B_303, A_304, C_305, D_301), F_302) | ~m1_subset_1(F_302, u1_struct_0(D_301)) | ~m1_subset_1(F_302, u1_struct_0(B_303)) | ~m1_pre_topc(D_301, B_303) | ~v1_tsep_1(D_301, B_303) | v2_struct_0(D_301) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_303), u1_struct_0(A_304)))) | ~v1_funct_2(C_305, u1_struct_0(B_303), u1_struct_0(A_304)) | ~v1_funct_1(C_305) | ~l1_pre_topc(B_303) | ~v2_pre_topc(B_303) | v2_struct_0(B_303) | ~l1_pre_topc(A_304) | ~v2_pre_topc(A_304) | v2_struct_0(A_304))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.21/1.53  tff(c_347, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_302, c_343])).
% 3.21/1.53  tff(c_354, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_106, c_87, c_38, c_36, c_34, c_205, c_28, c_26, c_70, c_347])).
% 3.21/1.53  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_42, c_46, c_144, c_354])).
% 3.21/1.53  tff(c_357, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 3.21/1.53  tff(c_524, plain, (![A_337, C_338, B_336, F_335, D_334]: (r1_tmap_1(D_334, A_337, k2_tmap_1(B_336, A_337, C_338, D_334), F_335) | ~r1_tmap_1(B_336, A_337, C_338, F_335) | ~m1_subset_1(F_335, u1_struct_0(D_334)) | ~m1_subset_1(F_335, u1_struct_0(B_336)) | ~m1_pre_topc(D_334, B_336) | ~v1_tsep_1(D_334, B_336) | v2_struct_0(D_334) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_336), u1_struct_0(A_337)))) | ~v1_funct_2(C_338, u1_struct_0(B_336), u1_struct_0(A_337)) | ~v1_funct_1(C_338) | ~l1_pre_topc(B_336) | ~v2_pre_topc(B_336) | v2_struct_0(B_336) | ~l1_pre_topc(A_337) | ~v2_pre_topc(A_337) | v2_struct_0(A_337))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.21/1.53  tff(c_526, plain, (![D_334, F_335]: (r1_tmap_1(D_334, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_334), F_335) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_335) | ~m1_subset_1(F_335, u1_struct_0(D_334)) | ~m1_subset_1(F_335, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_334, '#skF_4') | ~v1_tsep_1(D_334, '#skF_4') | v2_struct_0(D_334) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_524])).
% 3.21/1.53  tff(c_529, plain, (![D_334, F_335]: (r1_tmap_1(D_334, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_334), F_335) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_335) | ~m1_subset_1(F_335, u1_struct_0(D_334)) | ~m1_subset_1(F_335, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_334, '#skF_4') | ~v1_tsep_1(D_334, '#skF_4') | v2_struct_0(D_334) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_106, c_87, c_38, c_36, c_526])).
% 3.21/1.53  tff(c_558, plain, (![D_340, F_341]: (r1_tmap_1(D_340, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_340), F_341) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_341) | ~m1_subset_1(F_341, u1_struct_0(D_340)) | ~m1_subset_1(F_341, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_340, '#skF_4') | ~v1_tsep_1(D_340, '#skF_4') | v2_struct_0(D_340))), inference(negUnitSimplification, [status(thm)], [c_58, c_42, c_529])).
% 3.21/1.53  tff(c_472, plain, (![C_331, D_327, E_330, A_328, B_329]: (k3_tmap_1(A_328, B_329, C_331, D_327, E_330)=k2_partfun1(u1_struct_0(C_331), u1_struct_0(B_329), E_330, u1_struct_0(D_327)) | ~m1_pre_topc(D_327, C_331) | ~m1_subset_1(E_330, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_331), u1_struct_0(B_329)))) | ~v1_funct_2(E_330, u1_struct_0(C_331), u1_struct_0(B_329)) | ~v1_funct_1(E_330) | ~m1_pre_topc(D_327, A_328) | ~m1_pre_topc(C_331, A_328) | ~l1_pre_topc(B_329) | ~v2_pre_topc(B_329) | v2_struct_0(B_329) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328) | v2_struct_0(A_328))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.53  tff(c_474, plain, (![A_328, D_327]: (k3_tmap_1(A_328, '#skF_1', '#skF_4', D_327, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_327)) | ~m1_pre_topc(D_327, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_327, A_328) | ~m1_pre_topc('#skF_4', A_328) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328) | v2_struct_0(A_328))), inference(resolution, [status(thm)], [c_34, c_472])).
% 3.21/1.53  tff(c_477, plain, (![A_328, D_327]: (k3_tmap_1(A_328, '#skF_1', '#skF_4', D_327, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_327)) | ~m1_pre_topc(D_327, '#skF_4') | ~m1_pre_topc(D_327, A_328) | ~m1_pre_topc('#skF_4', A_328) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328) | v2_struct_0(A_328))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_38, c_36, c_474])).
% 3.21/1.53  tff(c_479, plain, (![A_332, D_333]: (k3_tmap_1(A_332, '#skF_1', '#skF_4', D_333, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_333)) | ~m1_pre_topc(D_333, '#skF_4') | ~m1_pre_topc(D_333, A_332) | ~m1_pre_topc('#skF_4', A_332) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(negUnitSimplification, [status(thm)], [c_58, c_477])).
% 3.21/1.53  tff(c_485, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_479])).
% 3.21/1.53  tff(c_497, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_28, c_485])).
% 3.21/1.53  tff(c_498, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_497])).
% 3.21/1.53  tff(c_436, plain, (![A_319, B_320, C_321, D_322]: (k2_partfun1(u1_struct_0(A_319), u1_struct_0(B_320), C_321, u1_struct_0(D_322))=k2_tmap_1(A_319, B_320, C_321, D_322) | ~m1_pre_topc(D_322, A_319) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_319), u1_struct_0(B_320)))) | ~v1_funct_2(C_321, u1_struct_0(A_319), u1_struct_0(B_320)) | ~v1_funct_1(C_321) | ~l1_pre_topc(B_320) | ~v2_pre_topc(B_320) | v2_struct_0(B_320) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.53  tff(c_438, plain, (![D_322]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_322))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_322) | ~m1_pre_topc(D_322, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_436])).
% 3.21/1.53  tff(c_441, plain, (![D_322]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_322))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_322) | ~m1_pre_topc(D_322, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_87, c_56, c_54, c_38, c_36, c_438])).
% 3.21/1.53  tff(c_442, plain, (![D_322]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_322))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_322) | ~m1_pre_topc(D_322, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_58, c_441])).
% 3.21/1.53  tff(c_506, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_498, c_442])).
% 3.21/1.53  tff(c_513, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_506])).
% 3.21/1.53  tff(c_358, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 3.21/1.53  tff(c_518, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_358])).
% 3.21/1.53  tff(c_561, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_558, c_518])).
% 3.21/1.53  tff(c_564, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_421, c_28, c_26, c_70, c_357, c_561])).
% 3.21/1.53  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_564])).
% 3.21/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.53  
% 3.21/1.53  Inference rules
% 3.21/1.53  ----------------------
% 3.21/1.53  #Ref     : 0
% 3.21/1.53  #Sup     : 89
% 3.21/1.53  #Fact    : 0
% 3.21/1.53  #Define  : 0
% 3.21/1.53  #Split   : 5
% 3.21/1.53  #Chain   : 0
% 3.21/1.53  #Close   : 0
% 3.21/1.53  
% 3.21/1.53  Ordering : KBO
% 3.21/1.53  
% 3.21/1.53  Simplification rules
% 3.21/1.53  ----------------------
% 3.21/1.53  #Subsume      : 11
% 3.54/1.53  #Demod        : 202
% 3.54/1.53  #Tautology    : 42
% 3.54/1.53  #SimpNegUnit  : 31
% 3.54/1.53  #BackRed      : 4
% 3.54/1.53  
% 3.54/1.53  #Partial instantiations: 0
% 3.54/1.53  #Strategies tried      : 1
% 3.54/1.53  
% 3.54/1.53  Timing (in seconds)
% 3.54/1.53  ----------------------
% 3.54/1.53  Preprocessing        : 0.39
% 3.54/1.54  Parsing              : 0.20
% 3.54/1.54  CNF conversion       : 0.05
% 3.54/1.54  Main loop            : 0.35
% 3.54/1.54  Inferencing          : 0.12
% 3.54/1.54  Reduction            : 0.12
% 3.54/1.54  Demodulation         : 0.09
% 3.54/1.54  BG Simplification    : 0.02
% 3.54/1.54  Subsumption          : 0.07
% 3.54/1.54  Abstraction          : 0.01
% 3.54/1.54  MUC search           : 0.00
% 3.54/1.54  Cooper               : 0.00
% 3.54/1.54  Total                : 0.79
% 3.54/1.54  Index Insertion      : 0.00
% 3.54/1.54  Index Deletion       : 0.00
% 3.54/1.54  Index Matching       : 0.00
% 3.54/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
