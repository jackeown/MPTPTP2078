%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:41 EST 2020

% Result     : Theorem 14.83s
% Output     : CNFRefutation 14.83s
% Verified   : 
% Statistics : Number of formulae       :  151 (1535 expanded)
%              Number of leaves         :   44 ( 555 expanded)
%              Depth                    :   19
%              Number of atoms          :  476 (7424 expanded)
%              Number of equality atoms :   39 ( 855 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_286,negated_conjecture,(
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
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_183,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_179,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_172,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_154,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> ( v1_tsep_1(C,A)
                    & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_98,axiom,(
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

tff(f_130,axiom,(
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

tff(f_225,axiom,(
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

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_46,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_80,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_78,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_161,plain,(
    ! [B_277,A_278] :
      ( v2_pre_topc(B_277)
      | ~ m1_pre_topc(B_277,A_278)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_167,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_161])).

tff(c_174,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_167])).

tff(c_119,plain,(
    ! [B_274,A_275] :
      ( l1_pre_topc(B_274)
      | ~ m1_pre_topc(B_274,A_275)
      | ~ l1_pre_topc(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_125,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_119])).

tff(c_132,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_125])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_95,plain,(
    ! [A_272] :
      ( u1_struct_0(A_272) = k2_struct_0(A_272)
      | ~ l1_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_99,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_139,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_99])).

tff(c_100,plain,(
    ! [A_273] :
      ( u1_struct_0(A_273) = k2_struct_0(A_273)
      | ~ l1_pre_topc(A_273) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_107,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_100])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_110,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_60])).

tff(c_144,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_110])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_109,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_58])).

tff(c_178,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_109])).

tff(c_38,plain,(
    ! [A_79] :
      ( m1_pre_topc(A_79,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_179,plain,(
    ! [B_279,A_280] :
      ( m1_subset_1(u1_struct_0(B_279),k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ m1_pre_topc(B_279,A_280)
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_191,plain,(
    ! [B_279] :
      ( m1_subset_1(u1_struct_0(B_279),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_279,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_179])).

tff(c_225,plain,(
    ! [B_282] :
      ( m1_subset_1(u1_struct_0(B_282),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_282,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_191])).

tff(c_231,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_225])).

tff(c_631,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_675,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_631])).

tff(c_679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_675])).

tff(c_681,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_16,plain,(
    ! [A_15] :
      ( v3_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    ! [B_78,A_76] :
      ( m1_subset_1(u1_struct_0(B_78),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_78,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_743,plain,(
    ! [B_303,A_304] :
      ( v1_tsep_1(B_303,A_304)
      | ~ v3_pre_topc(u1_struct_0(B_303),A_304)
      | ~ m1_subset_1(u1_struct_0(B_303),k1_zfmisc_1(u1_struct_0(A_304)))
      | ~ m1_pre_topc(B_303,A_304)
      | ~ l1_pre_topc(A_304)
      | ~ v2_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1460,plain,(
    ! [B_333,A_334] :
      ( v1_tsep_1(B_333,A_334)
      | ~ v3_pre_topc(u1_struct_0(B_333),A_334)
      | ~ v2_pre_topc(A_334)
      | ~ m1_pre_topc(B_333,A_334)
      | ~ l1_pre_topc(A_334) ) ),
    inference(resolution,[status(thm)],[c_36,c_743])).

tff(c_1491,plain,(
    ! [A_338] :
      ( v1_tsep_1('#skF_4',A_338)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_338)
      | ~ v2_pre_topc(A_338)
      | ~ m1_pre_topc('#skF_4',A_338)
      | ~ l1_pre_topc(A_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_1460])).

tff(c_1495,plain,
    ( v1_tsep_1('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1491])).

tff(c_1498,plain,(
    v1_tsep_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_132,c_681,c_1495])).

tff(c_68,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_170,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_161])).

tff(c_177,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_170])).

tff(c_128,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_119])).

tff(c_135,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_128])).

tff(c_143,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_99])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_150,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_56])).

tff(c_1499,plain,(
    ! [B_339,A_340] :
      ( v1_tsep_1(B_339,A_340)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(B_339),u1_pre_topc(B_339)),A_340)
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(B_339),u1_pre_topc(B_339)),A_340)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_339),u1_pre_topc(B_339)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(B_339),u1_pre_topc(B_339)))
      | ~ l1_pre_topc(B_339)
      | ~ v2_pre_topc(B_339)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1505,plain,(
    ! [A_340] :
      ( v1_tsep_1('#skF_3',A_340)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_340)
      | ~ v1_tsep_1(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_340)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_1499])).

tff(c_1517,plain,(
    ! [A_340] :
      ( v1_tsep_1('#skF_3',A_340)
      | ~ m1_pre_topc('#skF_4',A_340)
      | ~ v1_tsep_1('#skF_4',A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_135,c_174,c_150,c_143,c_132,c_150,c_143,c_150,c_150,c_143,c_1505])).

tff(c_393,plain,(
    ! [A_294,B_295] :
      ( m1_pre_topc(A_294,g1_pre_topc(u1_struct_0(B_295),u1_pre_topc(B_295)))
      | ~ m1_pre_topc(A_294,B_295)
      | ~ l1_pre_topc(B_295)
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_407,plain,(
    ! [A_294] :
      ( m1_pre_topc(A_294,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_294,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_393])).

tff(c_444,plain,(
    ! [A_296] :
      ( m1_pre_topc(A_296,'#skF_4')
      | ~ m1_pre_topc(A_296,'#skF_3')
      | ~ l1_pre_topc(A_296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_150,c_407])).

tff(c_454,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_444])).

tff(c_461,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_454])).

tff(c_228,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_225])).

tff(c_811,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_228])).

tff(c_530,plain,(
    ! [B_298,A_299] :
      ( v3_pre_topc(u1_struct_0(B_298),A_299)
      | ~ v1_tsep_1(B_298,A_299)
      | ~ m1_subset_1(u1_struct_0(B_298),k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ m1_pre_topc(B_298,A_299)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_545,plain,(
    ! [B_298] :
      ( v3_pre_topc(u1_struct_0(B_298),'#skF_4')
      | ~ v1_tsep_1(B_298,'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_298),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_298,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_530])).

tff(c_2036,plain,(
    ! [B_375] :
      ( v3_pre_topc(u1_struct_0(B_375),'#skF_4')
      | ~ v1_tsep_1(B_375,'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_375),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_375,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_132,c_545])).

tff(c_2042,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_2036])).

tff(c_2054,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_811,c_143,c_2042])).

tff(c_2066,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2054])).

tff(c_2069,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v1_tsep_1('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1517,c_2066])).

tff(c_2073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_132,c_1498,c_681,c_2069])).

tff(c_2075,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2054])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_145,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_54])).

tff(c_50,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_83,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52])).

tff(c_151,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_83])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1648,plain,(
    ! [A_347,B_348,C_349,D_350] :
      ( k2_partfun1(u1_struct_0(A_347),u1_struct_0(B_348),C_349,u1_struct_0(D_350)) = k2_tmap_1(A_347,B_348,C_349,D_350)
      | ~ m1_pre_topc(D_350,A_347)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_347),u1_struct_0(B_348))))
      | ~ v1_funct_2(C_349,u1_struct_0(A_347),u1_struct_0(B_348))
      | ~ v1_funct_1(C_349)
      | ~ l1_pre_topc(B_348)
      | ~ v2_pre_topc(B_348)
      | v2_struct_0(B_348)
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1664,plain,(
    ! [A_347,C_349,D_350] :
      ( k2_partfun1(u1_struct_0(A_347),u1_struct_0('#skF_2'),C_349,u1_struct_0(D_350)) = k2_tmap_1(A_347,'#skF_2',C_349,D_350)
      | ~ m1_pre_topc(D_350,A_347)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_347),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_349,u1_struct_0(A_347),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_349)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_1648])).

tff(c_1687,plain,(
    ! [A_347,C_349,D_350] :
      ( k2_partfun1(u1_struct_0(A_347),k2_struct_0('#skF_2'),C_349,u1_struct_0(D_350)) = k2_tmap_1(A_347,'#skF_2',C_349,D_350)
      | ~ m1_pre_topc(D_350,A_347)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_347),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_349,u1_struct_0(A_347),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_349)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_107,c_107,c_1664])).

tff(c_9839,plain,(
    ! [A_582,C_583,D_584] :
      ( k2_partfun1(u1_struct_0(A_582),k2_struct_0('#skF_2'),C_583,u1_struct_0(D_584)) = k2_tmap_1(A_582,'#skF_2',C_583,D_584)
      | ~ m1_pre_topc(D_584,A_582)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_582),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_583,u1_struct_0(A_582),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_583)
      | ~ l1_pre_topc(A_582)
      | ~ v2_pre_topc(A_582)
      | v2_struct_0(A_582) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1687])).

tff(c_9843,plain,(
    ! [C_583,D_584] :
      ( k2_partfun1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_583,u1_struct_0(D_584)) = k2_tmap_1('#skF_4','#skF_2',C_583,D_584)
      | ~ m1_pre_topc(D_584,'#skF_4')
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_583,u1_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_583)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_9839])).

tff(c_9852,plain,(
    ! [C_583,D_584] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_583,u1_struct_0(D_584)) = k2_tmap_1('#skF_4','#skF_2',C_583,D_584)
      | ~ m1_pre_topc(D_584,'#skF_4')
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_583,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_583)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_132,c_139,c_139,c_9843])).

tff(c_10046,plain,(
    ! [C_592,D_593] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_592,u1_struct_0(D_593)) = k2_tmap_1('#skF_4','#skF_2',C_592,D_593)
      | ~ m1_pre_topc(D_593,'#skF_4')
      | ~ m1_subset_1(C_592,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_592,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_592) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9852])).

tff(c_10048,plain,(
    ! [D_593] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_593)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_593)
      | ~ m1_pre_topc(D_593,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_178,c_10046])).

tff(c_10052,plain,(
    ! [D_594] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_594)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_594)
      | ~ m1_pre_topc(D_594,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_144,c_10048])).

tff(c_10061,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_10052])).

tff(c_10074,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_10061])).

tff(c_1803,plain,(
    ! [D_361,C_357,E_358,B_359,A_360] :
      ( k3_tmap_1(A_360,B_359,C_357,D_361,E_358) = k2_partfun1(u1_struct_0(C_357),u1_struct_0(B_359),E_358,u1_struct_0(D_361))
      | ~ m1_pre_topc(D_361,C_357)
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_357),u1_struct_0(B_359))))
      | ~ v1_funct_2(E_358,u1_struct_0(C_357),u1_struct_0(B_359))
      | ~ v1_funct_1(E_358)
      | ~ m1_pre_topc(D_361,A_360)
      | ~ m1_pre_topc(C_357,A_360)
      | ~ l1_pre_topc(B_359)
      | ~ v2_pre_topc(B_359)
      | v2_struct_0(B_359)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1809,plain,(
    ! [A_360,B_359,D_361,E_358] :
      ( k3_tmap_1(A_360,B_359,'#skF_4',D_361,E_358) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_359),E_358,u1_struct_0(D_361))
      | ~ m1_pre_topc(D_361,'#skF_4')
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_359))))
      | ~ v1_funct_2(E_358,u1_struct_0('#skF_4'),u1_struct_0(B_359))
      | ~ v1_funct_1(E_358)
      | ~ m1_pre_topc(D_361,A_360)
      | ~ m1_pre_topc('#skF_4',A_360)
      | ~ l1_pre_topc(B_359)
      | ~ v2_pre_topc(B_359)
      | v2_struct_0(B_359)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_1803])).

tff(c_23180,plain,(
    ! [A_841,B_842,D_843,E_844] :
      ( k3_tmap_1(A_841,B_842,'#skF_4',D_843,E_844) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_842),E_844,u1_struct_0(D_843))
      | ~ m1_pre_topc(D_843,'#skF_4')
      | ~ m1_subset_1(E_844,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_842))))
      | ~ v1_funct_2(E_844,k2_struct_0('#skF_4'),u1_struct_0(B_842))
      | ~ v1_funct_1(E_844)
      | ~ m1_pre_topc(D_843,A_841)
      | ~ m1_pre_topc('#skF_4',A_841)
      | ~ l1_pre_topc(B_842)
      | ~ v2_pre_topc(B_842)
      | v2_struct_0(B_842)
      | ~ l1_pre_topc(A_841)
      | ~ v2_pre_topc(A_841)
      | v2_struct_0(A_841) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_1809])).

tff(c_23188,plain,(
    ! [A_841,D_843,E_844] :
      ( k3_tmap_1(A_841,'#skF_2','#skF_4',D_843,E_844) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),E_844,u1_struct_0(D_843))
      | ~ m1_pre_topc(D_843,'#skF_4')
      | ~ m1_subset_1(E_844,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_844,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_844)
      | ~ m1_pre_topc(D_843,A_841)
      | ~ m1_pre_topc('#skF_4',A_841)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_841)
      | ~ v2_pre_topc(A_841)
      | v2_struct_0(A_841) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_23180])).

tff(c_23199,plain,(
    ! [A_841,D_843,E_844] :
      ( k3_tmap_1(A_841,'#skF_2','#skF_4',D_843,E_844) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_844,u1_struct_0(D_843))
      | ~ m1_pre_topc(D_843,'#skF_4')
      | ~ m1_subset_1(E_844,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_844,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_844)
      | ~ m1_pre_topc(D_843,A_841)
      | ~ m1_pre_topc('#skF_4',A_841)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_841)
      | ~ v2_pre_topc(A_841)
      | v2_struct_0(A_841) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_107,c_107,c_23188])).

tff(c_25704,plain,(
    ! [A_981,D_982,E_983] :
      ( k3_tmap_1(A_981,'#skF_2','#skF_4',D_982,E_983) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_983,u1_struct_0(D_982))
      | ~ m1_pre_topc(D_982,'#skF_4')
      | ~ m1_subset_1(E_983,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_983,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_983)
      | ~ m1_pre_topc(D_982,A_981)
      | ~ m1_pre_topc('#skF_4',A_981)
      | ~ l1_pre_topc(A_981)
      | ~ v2_pre_topc(A_981)
      | v2_struct_0(A_981) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_23199])).

tff(c_25706,plain,(
    ! [A_981,D_982] :
      ( k3_tmap_1(A_981,'#skF_2','#skF_4',D_982,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_982))
      | ~ m1_pre_topc(D_982,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_982,A_981)
      | ~ m1_pre_topc('#skF_4',A_981)
      | ~ l1_pre_topc(A_981)
      | ~ v2_pre_topc(A_981)
      | v2_struct_0(A_981) ) ),
    inference(resolution,[status(thm)],[c_178,c_25704])).

tff(c_25710,plain,(
    ! [A_984,D_985] :
      ( k3_tmap_1(A_984,'#skF_2','#skF_4',D_985,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_985))
      | ~ m1_pre_topc(D_985,'#skF_4')
      | ~ m1_pre_topc(D_985,A_984)
      | ~ m1_pre_topc('#skF_4',A_984)
      | ~ l1_pre_topc(A_984)
      | ~ v2_pre_topc(A_984)
      | v2_struct_0(A_984) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_144,c_25706])).

tff(c_25812,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_25710])).

tff(c_25932,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_64,c_461,c_10074,c_143,c_25812])).

tff(c_25933,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_25932])).

tff(c_48,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_84,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_25981,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25933,c_84])).

tff(c_40,plain,(
    ! [C_128,F_142,D_136,A_80,B_112] :
      ( r1_tmap_1(B_112,A_80,C_128,F_142)
      | ~ r1_tmap_1(D_136,A_80,k2_tmap_1(B_112,A_80,C_128,D_136),F_142)
      | ~ m1_subset_1(F_142,u1_struct_0(D_136))
      | ~ m1_subset_1(F_142,u1_struct_0(B_112))
      | ~ m1_pre_topc(D_136,B_112)
      | ~ v1_tsep_1(D_136,B_112)
      | v2_struct_0(D_136)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_112),u1_struct_0(A_80))))
      | ~ v1_funct_2(C_128,u1_struct_0(B_112),u1_struct_0(A_80))
      | ~ v1_funct_1(C_128)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_25987,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_25981,c_40])).

tff(c_25990,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_174,c_132,c_62,c_144,c_107,c_139,c_178,c_107,c_139,c_2075,c_461,c_145,c_139,c_151,c_143,c_25987])).

tff(c_25992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_66,c_70,c_46,c_25990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:13:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.83/7.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.83/7.24  
% 14.83/7.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.83/7.24  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.83/7.24  
% 14.83/7.24  %Foreground sorts:
% 14.83/7.24  
% 14.83/7.24  
% 14.83/7.24  %Background operators:
% 14.83/7.24  
% 14.83/7.24  
% 14.83/7.24  %Foreground operators:
% 14.83/7.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.83/7.24  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 14.83/7.24  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 14.83/7.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.83/7.24  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 14.83/7.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.83/7.24  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 14.83/7.24  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 14.83/7.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.83/7.24  tff('#skF_7', type, '#skF_7': $i).
% 14.83/7.24  tff('#skF_5', type, '#skF_5': $i).
% 14.83/7.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.83/7.24  tff('#skF_6', type, '#skF_6': $i).
% 14.83/7.24  tff('#skF_2', type, '#skF_2': $i).
% 14.83/7.24  tff('#skF_3', type, '#skF_3': $i).
% 14.83/7.24  tff('#skF_1', type, '#skF_1': $i).
% 14.83/7.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.83/7.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.83/7.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.83/7.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.83/7.24  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 14.83/7.24  tff('#skF_4', type, '#skF_4': $i).
% 14.83/7.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.83/7.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 14.83/7.24  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 14.83/7.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.83/7.24  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 14.83/7.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.83/7.24  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.83/7.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.83/7.24  
% 14.83/7.27  tff(f_286, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 14.83/7.27  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 14.83/7.27  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 14.83/7.27  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 14.83/7.27  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 14.83/7.27  tff(f_183, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 14.83/7.27  tff(f_179, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 14.83/7.27  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 14.83/7.27  tff(f_172, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 14.83/7.27  tff(f_154, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tmap_1)).
% 14.83/7.27  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 14.83/7.27  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 14.83/7.27  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 14.83/7.27  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 14.83/7.27  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_46, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_80, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_78, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_161, plain, (![B_277, A_278]: (v2_pre_topc(B_277) | ~m1_pre_topc(B_277, A_278) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.83/7.27  tff(c_167, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_161])).
% 14.83/7.27  tff(c_174, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_167])).
% 14.83/7.27  tff(c_119, plain, (![B_274, A_275]: (l1_pre_topc(B_274) | ~m1_pre_topc(B_274, A_275) | ~l1_pre_topc(A_275))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.83/7.27  tff(c_125, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_119])).
% 14.83/7.27  tff(c_132, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_125])).
% 14.83/7.27  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.83/7.27  tff(c_95, plain, (![A_272]: (u1_struct_0(A_272)=k2_struct_0(A_272) | ~l1_struct_0(A_272))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.83/7.27  tff(c_99, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_95])).
% 14.83/7.27  tff(c_139, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_132, c_99])).
% 14.83/7.27  tff(c_100, plain, (![A_273]: (u1_struct_0(A_273)=k2_struct_0(A_273) | ~l1_pre_topc(A_273))), inference(resolution, [status(thm)], [c_6, c_95])).
% 14.83/7.27  tff(c_107, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_100])).
% 14.83/7.27  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_110, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_60])).
% 14.83/7.27  tff(c_144, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_110])).
% 14.83/7.27  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_109, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_58])).
% 14.83/7.27  tff(c_178, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_109])).
% 14.83/7.27  tff(c_38, plain, (![A_79]: (m1_pre_topc(A_79, A_79) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_183])).
% 14.83/7.27  tff(c_179, plain, (![B_279, A_280]: (m1_subset_1(u1_struct_0(B_279), k1_zfmisc_1(u1_struct_0(A_280))) | ~m1_pre_topc(B_279, A_280) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.83/7.27  tff(c_191, plain, (![B_279]: (m1_subset_1(u1_struct_0(B_279), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_279, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_179])).
% 14.83/7.27  tff(c_225, plain, (![B_282]: (m1_subset_1(u1_struct_0(B_282), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_282, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_191])).
% 14.83/7.27  tff(c_231, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_139, c_225])).
% 14.83/7.27  tff(c_631, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_231])).
% 14.83/7.27  tff(c_675, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_38, c_631])).
% 14.83/7.27  tff(c_679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_675])).
% 14.83/7.27  tff(c_681, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_231])).
% 14.83/7.27  tff(c_16, plain, (![A_15]: (v3_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.83/7.27  tff(c_36, plain, (![B_78, A_76]: (m1_subset_1(u1_struct_0(B_78), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc(B_78, A_76) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.83/7.27  tff(c_743, plain, (![B_303, A_304]: (v1_tsep_1(B_303, A_304) | ~v3_pre_topc(u1_struct_0(B_303), A_304) | ~m1_subset_1(u1_struct_0(B_303), k1_zfmisc_1(u1_struct_0(A_304))) | ~m1_pre_topc(B_303, A_304) | ~l1_pre_topc(A_304) | ~v2_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_172])).
% 14.83/7.27  tff(c_1460, plain, (![B_333, A_334]: (v1_tsep_1(B_333, A_334) | ~v3_pre_topc(u1_struct_0(B_333), A_334) | ~v2_pre_topc(A_334) | ~m1_pre_topc(B_333, A_334) | ~l1_pre_topc(A_334))), inference(resolution, [status(thm)], [c_36, c_743])).
% 14.83/7.27  tff(c_1491, plain, (![A_338]: (v1_tsep_1('#skF_4', A_338) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_338) | ~v2_pre_topc(A_338) | ~m1_pre_topc('#skF_4', A_338) | ~l1_pre_topc(A_338))), inference(superposition, [status(thm), theory('equality')], [c_139, c_1460])).
% 14.83/7.27  tff(c_1495, plain, (v1_tsep_1('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_1491])).
% 14.83/7.27  tff(c_1498, plain, (v1_tsep_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_132, c_681, c_1495])).
% 14.83/7.27  tff(c_68, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_170, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_161])).
% 14.83/7.27  tff(c_177, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_170])).
% 14.83/7.27  tff(c_128, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_119])).
% 14.83/7.27  tff(c_135, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_128])).
% 14.83/7.27  tff(c_143, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_135, c_99])).
% 14.83/7.27  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_150, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_56])).
% 14.83/7.27  tff(c_1499, plain, (![B_339, A_340]: (v1_tsep_1(B_339, A_340) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(B_339), u1_pre_topc(B_339)), A_340) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(B_339), u1_pre_topc(B_339)), A_340) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_339), u1_pre_topc(B_339))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(B_339), u1_pre_topc(B_339))) | ~l1_pre_topc(B_339) | ~v2_pre_topc(B_339) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340))), inference(cnfTransformation, [status(thm)], [f_154])).
% 14.83/7.27  tff(c_1505, plain, (![A_340]: (v1_tsep_1('#skF_3', A_340) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_340) | ~v1_tsep_1(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_340) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340))), inference(superposition, [status(thm), theory('equality')], [c_143, c_1499])).
% 14.83/7.27  tff(c_1517, plain, (![A_340]: (v1_tsep_1('#skF_3', A_340) | ~m1_pre_topc('#skF_4', A_340) | ~v1_tsep_1('#skF_4', A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_135, c_174, c_150, c_143, c_132, c_150, c_143, c_150, c_150, c_143, c_1505])).
% 14.83/7.27  tff(c_393, plain, (![A_294, B_295]: (m1_pre_topc(A_294, g1_pre_topc(u1_struct_0(B_295), u1_pre_topc(B_295))) | ~m1_pre_topc(A_294, B_295) | ~l1_pre_topc(B_295) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.83/7.27  tff(c_407, plain, (![A_294]: (m1_pre_topc(A_294, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_294, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_294))), inference(superposition, [status(thm), theory('equality')], [c_143, c_393])).
% 14.83/7.27  tff(c_444, plain, (![A_296]: (m1_pre_topc(A_296, '#skF_4') | ~m1_pre_topc(A_296, '#skF_3') | ~l1_pre_topc(A_296))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_150, c_407])).
% 14.83/7.27  tff(c_454, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_444])).
% 14.83/7.27  tff(c_461, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_454])).
% 14.83/7.27  tff(c_228, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_143, c_225])).
% 14.83/7.27  tff(c_811, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_228])).
% 14.83/7.27  tff(c_530, plain, (![B_298, A_299]: (v3_pre_topc(u1_struct_0(B_298), A_299) | ~v1_tsep_1(B_298, A_299) | ~m1_subset_1(u1_struct_0(B_298), k1_zfmisc_1(u1_struct_0(A_299))) | ~m1_pre_topc(B_298, A_299) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_172])).
% 14.83/7.27  tff(c_545, plain, (![B_298]: (v3_pre_topc(u1_struct_0(B_298), '#skF_4') | ~v1_tsep_1(B_298, '#skF_4') | ~m1_subset_1(u1_struct_0(B_298), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_298, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_530])).
% 14.83/7.27  tff(c_2036, plain, (![B_375]: (v3_pre_topc(u1_struct_0(B_375), '#skF_4') | ~v1_tsep_1(B_375, '#skF_4') | ~m1_subset_1(u1_struct_0(B_375), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_375, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_132, c_545])).
% 14.83/7.27  tff(c_2042, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_143, c_2036])).
% 14.83/7.27  tff(c_2054, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_811, c_143, c_2042])).
% 14.83/7.27  tff(c_2066, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_2054])).
% 14.83/7.27  tff(c_2069, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~v1_tsep_1('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1517, c_2066])).
% 14.83/7.27  tff(c_2073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_132, c_1498, c_681, c_2069])).
% 14.83/7.27  tff(c_2075, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_2054])).
% 14.83/7.27  tff(c_54, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_145, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_54])).
% 14.83/7.27  tff(c_50, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_52, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_83, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52])).
% 14.83/7.27  tff(c_151, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_83])).
% 14.83/7.27  tff(c_82, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_1648, plain, (![A_347, B_348, C_349, D_350]: (k2_partfun1(u1_struct_0(A_347), u1_struct_0(B_348), C_349, u1_struct_0(D_350))=k2_tmap_1(A_347, B_348, C_349, D_350) | ~m1_pre_topc(D_350, A_347) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_347), u1_struct_0(B_348)))) | ~v1_funct_2(C_349, u1_struct_0(A_347), u1_struct_0(B_348)) | ~v1_funct_1(C_349) | ~l1_pre_topc(B_348) | ~v2_pre_topc(B_348) | v2_struct_0(B_348) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.83/7.27  tff(c_1664, plain, (![A_347, C_349, D_350]: (k2_partfun1(u1_struct_0(A_347), u1_struct_0('#skF_2'), C_349, u1_struct_0(D_350))=k2_tmap_1(A_347, '#skF_2', C_349, D_350) | ~m1_pre_topc(D_350, A_347) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_347), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_349, u1_struct_0(A_347), u1_struct_0('#skF_2')) | ~v1_funct_1(C_349) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(superposition, [status(thm), theory('equality')], [c_107, c_1648])).
% 14.83/7.27  tff(c_1687, plain, (![A_347, C_349, D_350]: (k2_partfun1(u1_struct_0(A_347), k2_struct_0('#skF_2'), C_349, u1_struct_0(D_350))=k2_tmap_1(A_347, '#skF_2', C_349, D_350) | ~m1_pre_topc(D_350, A_347) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_347), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_349, u1_struct_0(A_347), k2_struct_0('#skF_2')) | ~v1_funct_1(C_349) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_107, c_107, c_1664])).
% 14.83/7.27  tff(c_9839, plain, (![A_582, C_583, D_584]: (k2_partfun1(u1_struct_0(A_582), k2_struct_0('#skF_2'), C_583, u1_struct_0(D_584))=k2_tmap_1(A_582, '#skF_2', C_583, D_584) | ~m1_pre_topc(D_584, A_582) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_582), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_583, u1_struct_0(A_582), k2_struct_0('#skF_2')) | ~v1_funct_1(C_583) | ~l1_pre_topc(A_582) | ~v2_pre_topc(A_582) | v2_struct_0(A_582))), inference(negUnitSimplification, [status(thm)], [c_76, c_1687])).
% 14.83/7.27  tff(c_9843, plain, (![C_583, D_584]: (k2_partfun1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_583, u1_struct_0(D_584))=k2_tmap_1('#skF_4', '#skF_2', C_583, D_584) | ~m1_pre_topc(D_584, '#skF_4') | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_583, u1_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_583) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_9839])).
% 14.83/7.27  tff(c_9852, plain, (![C_583, D_584]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_583, u1_struct_0(D_584))=k2_tmap_1('#skF_4', '#skF_2', C_583, D_584) | ~m1_pre_topc(D_584, '#skF_4') | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_583, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_583) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_132, c_139, c_139, c_9843])).
% 14.83/7.27  tff(c_10046, plain, (![C_592, D_593]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_592, u1_struct_0(D_593))=k2_tmap_1('#skF_4', '#skF_2', C_592, D_593) | ~m1_pre_topc(D_593, '#skF_4') | ~m1_subset_1(C_592, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_592, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_592))), inference(negUnitSimplification, [status(thm)], [c_66, c_9852])).
% 14.83/7.27  tff(c_10048, plain, (![D_593]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_593))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_593) | ~m1_pre_topc(D_593, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_178, c_10046])).
% 14.83/7.27  tff(c_10052, plain, (![D_594]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_594))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_594) | ~m1_pre_topc(D_594, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_144, c_10048])).
% 14.83/7.27  tff(c_10061, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_143, c_10052])).
% 14.83/7.27  tff(c_10074, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_10061])).
% 14.83/7.27  tff(c_1803, plain, (![D_361, C_357, E_358, B_359, A_360]: (k3_tmap_1(A_360, B_359, C_357, D_361, E_358)=k2_partfun1(u1_struct_0(C_357), u1_struct_0(B_359), E_358, u1_struct_0(D_361)) | ~m1_pre_topc(D_361, C_357) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_357), u1_struct_0(B_359)))) | ~v1_funct_2(E_358, u1_struct_0(C_357), u1_struct_0(B_359)) | ~v1_funct_1(E_358) | ~m1_pre_topc(D_361, A_360) | ~m1_pre_topc(C_357, A_360) | ~l1_pre_topc(B_359) | ~v2_pre_topc(B_359) | v2_struct_0(B_359) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.83/7.27  tff(c_1809, plain, (![A_360, B_359, D_361, E_358]: (k3_tmap_1(A_360, B_359, '#skF_4', D_361, E_358)=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_359), E_358, u1_struct_0(D_361)) | ~m1_pre_topc(D_361, '#skF_4') | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_359)))) | ~v1_funct_2(E_358, u1_struct_0('#skF_4'), u1_struct_0(B_359)) | ~v1_funct_1(E_358) | ~m1_pre_topc(D_361, A_360) | ~m1_pre_topc('#skF_4', A_360) | ~l1_pre_topc(B_359) | ~v2_pre_topc(B_359) | v2_struct_0(B_359) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(superposition, [status(thm), theory('equality')], [c_139, c_1803])).
% 14.83/7.27  tff(c_23180, plain, (![A_841, B_842, D_843, E_844]: (k3_tmap_1(A_841, B_842, '#skF_4', D_843, E_844)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_842), E_844, u1_struct_0(D_843)) | ~m1_pre_topc(D_843, '#skF_4') | ~m1_subset_1(E_844, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_842)))) | ~v1_funct_2(E_844, k2_struct_0('#skF_4'), u1_struct_0(B_842)) | ~v1_funct_1(E_844) | ~m1_pre_topc(D_843, A_841) | ~m1_pre_topc('#skF_4', A_841) | ~l1_pre_topc(B_842) | ~v2_pre_topc(B_842) | v2_struct_0(B_842) | ~l1_pre_topc(A_841) | ~v2_pre_topc(A_841) | v2_struct_0(A_841))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_1809])).
% 14.83/7.27  tff(c_23188, plain, (![A_841, D_843, E_844]: (k3_tmap_1(A_841, '#skF_2', '#skF_4', D_843, E_844)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), E_844, u1_struct_0(D_843)) | ~m1_pre_topc(D_843, '#skF_4') | ~m1_subset_1(E_844, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_844, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_844) | ~m1_pre_topc(D_843, A_841) | ~m1_pre_topc('#skF_4', A_841) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_841) | ~v2_pre_topc(A_841) | v2_struct_0(A_841))), inference(superposition, [status(thm), theory('equality')], [c_107, c_23180])).
% 14.83/7.27  tff(c_23199, plain, (![A_841, D_843, E_844]: (k3_tmap_1(A_841, '#skF_2', '#skF_4', D_843, E_844)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_844, u1_struct_0(D_843)) | ~m1_pre_topc(D_843, '#skF_4') | ~m1_subset_1(E_844, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_844, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_844) | ~m1_pre_topc(D_843, A_841) | ~m1_pre_topc('#skF_4', A_841) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_841) | ~v2_pre_topc(A_841) | v2_struct_0(A_841))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_107, c_107, c_23188])).
% 14.83/7.27  tff(c_25704, plain, (![A_981, D_982, E_983]: (k3_tmap_1(A_981, '#skF_2', '#skF_4', D_982, E_983)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_983, u1_struct_0(D_982)) | ~m1_pre_topc(D_982, '#skF_4') | ~m1_subset_1(E_983, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_983, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_983) | ~m1_pre_topc(D_982, A_981) | ~m1_pre_topc('#skF_4', A_981) | ~l1_pre_topc(A_981) | ~v2_pre_topc(A_981) | v2_struct_0(A_981))), inference(negUnitSimplification, [status(thm)], [c_76, c_23199])).
% 14.83/7.27  tff(c_25706, plain, (![A_981, D_982]: (k3_tmap_1(A_981, '#skF_2', '#skF_4', D_982, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_982)) | ~m1_pre_topc(D_982, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_982, A_981) | ~m1_pre_topc('#skF_4', A_981) | ~l1_pre_topc(A_981) | ~v2_pre_topc(A_981) | v2_struct_0(A_981))), inference(resolution, [status(thm)], [c_178, c_25704])).
% 14.83/7.27  tff(c_25710, plain, (![A_984, D_985]: (k3_tmap_1(A_984, '#skF_2', '#skF_4', D_985, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_985)) | ~m1_pre_topc(D_985, '#skF_4') | ~m1_pre_topc(D_985, A_984) | ~m1_pre_topc('#skF_4', A_984) | ~l1_pre_topc(A_984) | ~v2_pre_topc(A_984) | v2_struct_0(A_984))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_144, c_25706])).
% 14.83/7.27  tff(c_25812, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_25710])).
% 14.83/7.27  tff(c_25932, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_64, c_461, c_10074, c_143, c_25812])).
% 14.83/7.27  tff(c_25933, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_82, c_25932])).
% 14.83/7.27  tff(c_48, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_286])).
% 14.83/7.27  tff(c_84, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 14.83/7.27  tff(c_25981, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25933, c_84])).
% 14.83/7.27  tff(c_40, plain, (![C_128, F_142, D_136, A_80, B_112]: (r1_tmap_1(B_112, A_80, C_128, F_142) | ~r1_tmap_1(D_136, A_80, k2_tmap_1(B_112, A_80, C_128, D_136), F_142) | ~m1_subset_1(F_142, u1_struct_0(D_136)) | ~m1_subset_1(F_142, u1_struct_0(B_112)) | ~m1_pre_topc(D_136, B_112) | ~v1_tsep_1(D_136, B_112) | v2_struct_0(D_136) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_112), u1_struct_0(A_80)))) | ~v1_funct_2(C_128, u1_struct_0(B_112), u1_struct_0(A_80)) | ~v1_funct_1(C_128) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_225])).
% 14.83/7.27  tff(c_25987, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_25981, c_40])).
% 14.83/7.27  tff(c_25990, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_174, c_132, c_62, c_144, c_107, c_139, c_178, c_107, c_139, c_2075, c_461, c_145, c_139, c_151, c_143, c_25987])).
% 14.83/7.27  tff(c_25992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_66, c_70, c_46, c_25990])).
% 14.83/7.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.83/7.27  
% 14.83/7.27  Inference rules
% 14.83/7.27  ----------------------
% 14.83/7.27  #Ref     : 0
% 14.83/7.27  #Sup     : 5724
% 14.83/7.27  #Fact    : 0
% 14.83/7.27  #Define  : 0
% 14.83/7.27  #Split   : 23
% 14.83/7.27  #Chain   : 0
% 14.83/7.27  #Close   : 0
% 14.83/7.27  
% 14.83/7.27  Ordering : KBO
% 14.83/7.27  
% 14.83/7.27  Simplification rules
% 14.83/7.27  ----------------------
% 14.83/7.27  #Subsume      : 3584
% 14.83/7.27  #Demod        : 11148
% 14.83/7.27  #Tautology    : 803
% 14.83/7.27  #SimpNegUnit  : 241
% 14.83/7.27  #BackRed      : 7
% 14.83/7.27  
% 14.83/7.27  #Partial instantiations: 0
% 14.83/7.27  #Strategies tried      : 1
% 14.83/7.27  
% 14.83/7.27  Timing (in seconds)
% 14.83/7.27  ----------------------
% 15.04/7.27  Preprocessing        : 0.42
% 15.04/7.27  Parsing              : 0.22
% 15.04/7.27  CNF conversion       : 0.05
% 15.04/7.27  Main loop            : 6.09
% 15.04/7.27  Inferencing          : 0.89
% 15.04/7.27  Reduction            : 2.00
% 15.04/7.27  Demodulation         : 1.57
% 15.04/7.27  BG Simplification    : 0.08
% 15.04/7.27  Subsumption          : 2.93
% 15.04/7.27  Abstraction          : 0.19
% 15.04/7.27  MUC search           : 0.00
% 15.04/7.27  Cooper               : 0.00
% 15.04/7.27  Total                : 6.56
% 15.04/7.27  Index Insertion      : 0.00
% 15.04/7.27  Index Deletion       : 0.00
% 15.04/7.27  Index Matching       : 0.00
% 15.04/7.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
