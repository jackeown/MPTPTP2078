%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:31 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 221 expanded)
%              Number of leaves         :   33 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  341 (1719 expanded)
%              Number of equality atoms :    6 (  74 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_256,negated_conjecture,(
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

tff(f_203,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( ( v1_tsep_1(C,D)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,B,E,F)
                                  <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_86,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_153,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_26,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_70,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_70])).

tff(c_146,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_73,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_64])).

tff(c_148,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_73])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_40,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_489,plain,(
    ! [D_493,A_491,C_494,G_495,B_496,E_492] :
      ( r1_tmap_1(D_493,B_496,E_492,G_495)
      | ~ r1_tmap_1(C_494,B_496,k3_tmap_1(A_491,B_496,D_493,C_494,E_492),G_495)
      | ~ m1_subset_1(G_495,u1_struct_0(C_494))
      | ~ m1_subset_1(G_495,u1_struct_0(D_493))
      | ~ m1_pre_topc(C_494,D_493)
      | ~ v1_tsep_1(C_494,D_493)
      | ~ m1_subset_1(E_492,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_493),u1_struct_0(B_496))))
      | ~ v1_funct_2(E_492,u1_struct_0(D_493),u1_struct_0(B_496))
      | ~ v1_funct_1(E_492)
      | ~ m1_pre_topc(D_493,A_491)
      | v2_struct_0(D_493)
      | ~ m1_pre_topc(C_494,A_491)
      | v2_struct_0(C_494)
      | ~ l1_pre_topc(B_496)
      | ~ v2_pre_topc(B_496)
      | v2_struct_0(B_496)
      | ~ l1_pre_topc(A_491)
      | ~ v2_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_493,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_146,c_489])).

tff(c_500,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_60,c_58,c_48,c_44,c_42,c_40,c_38,c_32,c_30,c_74,c_493])).

tff(c_501,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_50,c_46,c_148,c_500])).

tff(c_36,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_79,plain,(
    ! [B_420,A_421] :
      ( l1_pre_topc(B_420)
      | ~ m1_pre_topc(B_420,A_421)
      | ~ l1_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_79])).

tff(c_91,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_82])).

tff(c_98,plain,(
    ! [B_422,A_423] :
      ( v2_pre_topc(B_422)
      | ~ m1_pre_topc(B_422,A_423)
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_110,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_101])).

tff(c_16,plain,(
    ! [B_38,A_36] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_153,plain,(
    ! [B_435,A_436] :
      ( v3_pre_topc(u1_struct_0(B_435),A_436)
      | ~ v1_tsep_1(B_435,A_436)
      | ~ m1_subset_1(u1_struct_0(B_435),k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ m1_pre_topc(B_435,A_436)
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_157,plain,(
    ! [B_38,A_36] :
      ( v3_pre_topc(u1_struct_0(B_38),A_36)
      | ~ v1_tsep_1(B_38,A_36)
      | ~ v2_pre_topc(A_36)
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_16,c_153])).

tff(c_149,plain,(
    ! [C_432,A_433,B_434] :
      ( m1_subset_1(C_432,k1_zfmisc_1(u1_struct_0(A_433)))
      | ~ m1_subset_1(C_432,k1_zfmisc_1(u1_struct_0(B_434)))
      | ~ m1_pre_topc(B_434,A_433)
      | ~ l1_pre_topc(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_159,plain,(
    ! [B_439,A_440,A_441] :
      ( m1_subset_1(u1_struct_0(B_439),k1_zfmisc_1(u1_struct_0(A_440)))
      | ~ m1_pre_topc(A_441,A_440)
      | ~ l1_pre_topc(A_440)
      | ~ m1_pre_topc(B_439,A_441)
      | ~ l1_pre_topc(A_441) ) ),
    inference(resolution,[status(thm)],[c_16,c_149])).

tff(c_163,plain,(
    ! [B_439] :
      ( m1_subset_1(u1_struct_0(B_439),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_439,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_159])).

tff(c_173,plain,(
    ! [B_439] :
      ( m1_subset_1(u1_struct_0(B_439),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_439,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_52,c_163])).

tff(c_353,plain,(
    ! [D_469,C_470,A_471] :
      ( v3_pre_topc(D_469,C_470)
      | ~ m1_subset_1(D_469,k1_zfmisc_1(u1_struct_0(C_470)))
      | ~ v3_pre_topc(D_469,A_471)
      | ~ m1_pre_topc(C_470,A_471)
      | ~ m1_subset_1(D_469,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ l1_pre_topc(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_525,plain,(
    ! [B_500,A_501,A_502] :
      ( v3_pre_topc(u1_struct_0(B_500),A_501)
      | ~ v3_pre_topc(u1_struct_0(B_500),A_502)
      | ~ m1_pre_topc(A_501,A_502)
      | ~ m1_subset_1(u1_struct_0(B_500),k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ l1_pre_topc(A_502)
      | ~ m1_pre_topc(B_500,A_501)
      | ~ l1_pre_topc(A_501) ) ),
    inference(resolution,[status(thm)],[c_16,c_353])).

tff(c_529,plain,(
    ! [B_500] :
      ( v3_pre_topc(u1_struct_0(B_500),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_500),'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_500),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_500,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_525])).

tff(c_546,plain,(
    ! [B_503] :
      ( v3_pre_topc(u1_struct_0(B_503),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_503),'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_503),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_503,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_52,c_529])).

tff(c_583,plain,(
    ! [B_504] :
      ( v3_pre_topc(u1_struct_0(B_504),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_504),'#skF_2')
      | ~ m1_pre_topc(B_504,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_173,c_546])).

tff(c_587,plain,(
    ! [B_38] :
      ( v3_pre_topc(u1_struct_0(B_38),'#skF_4')
      | ~ m1_pre_topc(B_38,'#skF_4')
      | ~ v1_tsep_1(B_38,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_38,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_157,c_583])).

tff(c_591,plain,(
    ! [B_505] :
      ( v3_pre_topc(u1_struct_0(B_505),'#skF_4')
      | ~ m1_pre_topc(B_505,'#skF_4')
      | ~ v1_tsep_1(B_505,'#skF_2')
      | ~ m1_pre_topc(B_505,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_587])).

tff(c_204,plain,(
    ! [B_451,A_452] :
      ( v1_tsep_1(B_451,A_452)
      | ~ v3_pre_topc(u1_struct_0(B_451),A_452)
      | ~ m1_subset_1(u1_struct_0(B_451),k1_zfmisc_1(u1_struct_0(A_452)))
      | ~ m1_pre_topc(B_451,A_452)
      | ~ l1_pre_topc(A_452)
      | ~ v2_pre_topc(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_238,plain,(
    ! [B_38,A_36] :
      ( v1_tsep_1(B_38,A_36)
      | ~ v3_pre_topc(u1_struct_0(B_38),A_36)
      | ~ v2_pre_topc(A_36)
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_16,c_204])).

tff(c_598,plain,(
    ! [B_505] :
      ( v1_tsep_1(B_505,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_505,'#skF_4')
      | ~ v1_tsep_1(B_505,'#skF_2')
      | ~ m1_pre_topc(B_505,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_591,c_238])).

tff(c_657,plain,(
    ! [B_508] :
      ( v1_tsep_1(B_508,'#skF_4')
      | ~ m1_pre_topc(B_508,'#skF_4')
      | ~ v1_tsep_1(B_508,'#skF_2')
      | ~ m1_pre_topc(B_508,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_110,c_598])).

tff(c_660,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_657])).

tff(c_663,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_32,c_660])).

tff(c_665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_663])).

tff(c_666,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1022,plain,(
    ! [B_557,C_559,D_558,E_556,G_561,A_560] :
      ( r1_tmap_1(D_558,B_557,k3_tmap_1(A_560,B_557,C_559,D_558,E_556),G_561)
      | ~ r1_tmap_1(C_559,B_557,E_556,G_561)
      | ~ m1_pre_topc(D_558,C_559)
      | ~ m1_subset_1(G_561,u1_struct_0(D_558))
      | ~ m1_subset_1(G_561,u1_struct_0(C_559))
      | ~ m1_subset_1(E_556,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_559),u1_struct_0(B_557))))
      | ~ v1_funct_2(E_556,u1_struct_0(C_559),u1_struct_0(B_557))
      | ~ v1_funct_1(E_556)
      | ~ m1_pre_topc(D_558,A_560)
      | v2_struct_0(D_558)
      | ~ m1_pre_topc(C_559,A_560)
      | v2_struct_0(C_559)
      | ~ l1_pre_topc(B_557)
      | ~ v2_pre_topc(B_557)
      | v2_struct_0(B_557)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1024,plain,(
    ! [D_558,A_560,G_561] :
      ( r1_tmap_1(D_558,'#skF_1',k3_tmap_1(A_560,'#skF_1','#skF_4',D_558,'#skF_5'),G_561)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_561)
      | ~ m1_pre_topc(D_558,'#skF_4')
      | ~ m1_subset_1(G_561,u1_struct_0(D_558))
      | ~ m1_subset_1(G_561,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_558,A_560)
      | v2_struct_0(D_558)
      | ~ m1_pre_topc('#skF_4',A_560)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(resolution,[status(thm)],[c_38,c_1022])).

tff(c_1027,plain,(
    ! [D_558,A_560,G_561] :
      ( r1_tmap_1(D_558,'#skF_1',k3_tmap_1(A_560,'#skF_1','#skF_4',D_558,'#skF_5'),G_561)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_561)
      | ~ m1_pre_topc(D_558,'#skF_4')
      | ~ m1_subset_1(G_561,u1_struct_0(D_558))
      | ~ m1_subset_1(G_561,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_558,A_560)
      | v2_struct_0(D_558)
      | ~ m1_pre_topc('#skF_4',A_560)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_42,c_40,c_1024])).

tff(c_1036,plain,(
    ! [D_564,A_565,G_566] :
      ( r1_tmap_1(D_564,'#skF_1',k3_tmap_1(A_565,'#skF_1','#skF_4',D_564,'#skF_5'),G_566)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_566)
      | ~ m1_pre_topc(D_564,'#skF_4')
      | ~ m1_subset_1(G_566,u1_struct_0(D_564))
      | ~ m1_subset_1(G_566,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_564,A_565)
      | v2_struct_0(D_564)
      | ~ m1_pre_topc('#skF_4',A_565)
      | ~ l1_pre_topc(A_565)
      | ~ v2_pre_topc(A_565)
      | v2_struct_0(A_565) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_1027])).

tff(c_667,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1039,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1036,c_667])).

tff(c_1042,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_44,c_48,c_30,c_74,c_32,c_666,c_1039])).

tff(c_1044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_1042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.68  
% 3.85/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.69  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.85/1.69  
% 3.85/1.69  %Foreground sorts:
% 3.85/1.69  
% 3.85/1.69  
% 3.85/1.69  %Background operators:
% 3.85/1.69  
% 3.85/1.69  
% 3.85/1.69  %Foreground operators:
% 3.85/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.85/1.69  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.85/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.69  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.85/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.69  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.85/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.85/1.69  tff('#skF_7', type, '#skF_7': $i).
% 3.85/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.85/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.69  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.85/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.69  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.85/1.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.85/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.85/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.69  
% 4.19/1.73  tff(f_256, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tmap_1)).
% 4.19/1.73  tff(f_203, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.19/1.73  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.19/1.73  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.19/1.73  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.19/1.73  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.19/1.73  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.19/1.73  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 4.19/1.73  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.19/1.73  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_26, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_28, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_74, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 4.19/1.73  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_70, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_72, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_70])).
% 4.19/1.73  tff(c_146, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_72])).
% 4.19/1.73  tff(c_64, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_73, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_64])).
% 4.19/1.73  tff(c_148, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_73])).
% 4.19/1.73  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_40, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_489, plain, (![D_493, A_491, C_494, G_495, B_496, E_492]: (r1_tmap_1(D_493, B_496, E_492, G_495) | ~r1_tmap_1(C_494, B_496, k3_tmap_1(A_491, B_496, D_493, C_494, E_492), G_495) | ~m1_subset_1(G_495, u1_struct_0(C_494)) | ~m1_subset_1(G_495, u1_struct_0(D_493)) | ~m1_pre_topc(C_494, D_493) | ~v1_tsep_1(C_494, D_493) | ~m1_subset_1(E_492, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_493), u1_struct_0(B_496)))) | ~v1_funct_2(E_492, u1_struct_0(D_493), u1_struct_0(B_496)) | ~v1_funct_1(E_492) | ~m1_pre_topc(D_493, A_491) | v2_struct_0(D_493) | ~m1_pre_topc(C_494, A_491) | v2_struct_0(C_494) | ~l1_pre_topc(B_496) | ~v2_pre_topc(B_496) | v2_struct_0(B_496) | ~l1_pre_topc(A_491) | ~v2_pre_topc(A_491) | v2_struct_0(A_491))), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.19/1.73  tff(c_493, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_146, c_489])).
% 4.19/1.73  tff(c_500, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_60, c_58, c_48, c_44, c_42, c_40, c_38, c_32, c_30, c_74, c_493])).
% 4.19/1.73  tff(c_501, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_50, c_46, c_148, c_500])).
% 4.19/1.73  tff(c_36, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.19/1.73  tff(c_79, plain, (![B_420, A_421]: (l1_pre_topc(B_420) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.19/1.73  tff(c_82, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_79])).
% 4.19/1.73  tff(c_91, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_82])).
% 4.19/1.73  tff(c_98, plain, (![B_422, A_423]: (v2_pre_topc(B_422) | ~m1_pre_topc(B_422, A_423) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.19/1.73  tff(c_101, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_98])).
% 4.19/1.73  tff(c_110, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_101])).
% 4.19/1.73  tff(c_16, plain, (![B_38, A_36]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.19/1.73  tff(c_153, plain, (![B_435, A_436]: (v3_pre_topc(u1_struct_0(B_435), A_436) | ~v1_tsep_1(B_435, A_436) | ~m1_subset_1(u1_struct_0(B_435), k1_zfmisc_1(u1_struct_0(A_436))) | ~m1_pre_topc(B_435, A_436) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.19/1.73  tff(c_157, plain, (![B_38, A_36]: (v3_pre_topc(u1_struct_0(B_38), A_36) | ~v1_tsep_1(B_38, A_36) | ~v2_pre_topc(A_36) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_16, c_153])).
% 4.19/1.73  tff(c_149, plain, (![C_432, A_433, B_434]: (m1_subset_1(C_432, k1_zfmisc_1(u1_struct_0(A_433))) | ~m1_subset_1(C_432, k1_zfmisc_1(u1_struct_0(B_434))) | ~m1_pre_topc(B_434, A_433) | ~l1_pre_topc(A_433))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.19/1.73  tff(c_159, plain, (![B_439, A_440, A_441]: (m1_subset_1(u1_struct_0(B_439), k1_zfmisc_1(u1_struct_0(A_440))) | ~m1_pre_topc(A_441, A_440) | ~l1_pre_topc(A_440) | ~m1_pre_topc(B_439, A_441) | ~l1_pre_topc(A_441))), inference(resolution, [status(thm)], [c_16, c_149])).
% 4.19/1.73  tff(c_163, plain, (![B_439]: (m1_subset_1(u1_struct_0(B_439), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(B_439, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_159])).
% 4.19/1.73  tff(c_173, plain, (![B_439]: (m1_subset_1(u1_struct_0(B_439), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_439, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_52, c_163])).
% 4.19/1.73  tff(c_353, plain, (![D_469, C_470, A_471]: (v3_pre_topc(D_469, C_470) | ~m1_subset_1(D_469, k1_zfmisc_1(u1_struct_0(C_470))) | ~v3_pre_topc(D_469, A_471) | ~m1_pre_topc(C_470, A_471) | ~m1_subset_1(D_469, k1_zfmisc_1(u1_struct_0(A_471))) | ~l1_pre_topc(A_471))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.19/1.73  tff(c_525, plain, (![B_500, A_501, A_502]: (v3_pre_topc(u1_struct_0(B_500), A_501) | ~v3_pre_topc(u1_struct_0(B_500), A_502) | ~m1_pre_topc(A_501, A_502) | ~m1_subset_1(u1_struct_0(B_500), k1_zfmisc_1(u1_struct_0(A_502))) | ~l1_pre_topc(A_502) | ~m1_pre_topc(B_500, A_501) | ~l1_pre_topc(A_501))), inference(resolution, [status(thm)], [c_16, c_353])).
% 4.19/1.73  tff(c_529, plain, (![B_500]: (v3_pre_topc(u1_struct_0(B_500), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_500), '#skF_2') | ~m1_subset_1(u1_struct_0(B_500), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(B_500, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_525])).
% 4.19/1.73  tff(c_546, plain, (![B_503]: (v3_pre_topc(u1_struct_0(B_503), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_503), '#skF_2') | ~m1_subset_1(u1_struct_0(B_503), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_503, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_52, c_529])).
% 4.19/1.73  tff(c_583, plain, (![B_504]: (v3_pre_topc(u1_struct_0(B_504), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_504), '#skF_2') | ~m1_pre_topc(B_504, '#skF_4'))), inference(resolution, [status(thm)], [c_173, c_546])).
% 4.19/1.73  tff(c_587, plain, (![B_38]: (v3_pre_topc(u1_struct_0(B_38), '#skF_4') | ~m1_pre_topc(B_38, '#skF_4') | ~v1_tsep_1(B_38, '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc(B_38, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_157, c_583])).
% 4.19/1.73  tff(c_591, plain, (![B_505]: (v3_pre_topc(u1_struct_0(B_505), '#skF_4') | ~m1_pre_topc(B_505, '#skF_4') | ~v1_tsep_1(B_505, '#skF_2') | ~m1_pre_topc(B_505, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_587])).
% 4.19/1.73  tff(c_204, plain, (![B_451, A_452]: (v1_tsep_1(B_451, A_452) | ~v3_pre_topc(u1_struct_0(B_451), A_452) | ~m1_subset_1(u1_struct_0(B_451), k1_zfmisc_1(u1_struct_0(A_452))) | ~m1_pre_topc(B_451, A_452) | ~l1_pre_topc(A_452) | ~v2_pre_topc(A_452))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.19/1.73  tff(c_238, plain, (![B_38, A_36]: (v1_tsep_1(B_38, A_36) | ~v3_pre_topc(u1_struct_0(B_38), A_36) | ~v2_pre_topc(A_36) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_16, c_204])).
% 4.19/1.73  tff(c_598, plain, (![B_505]: (v1_tsep_1(B_505, '#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(B_505, '#skF_4') | ~v1_tsep_1(B_505, '#skF_2') | ~m1_pre_topc(B_505, '#skF_2'))), inference(resolution, [status(thm)], [c_591, c_238])).
% 4.19/1.73  tff(c_657, plain, (![B_508]: (v1_tsep_1(B_508, '#skF_4') | ~m1_pre_topc(B_508, '#skF_4') | ~v1_tsep_1(B_508, '#skF_2') | ~m1_pre_topc(B_508, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_110, c_598])).
% 4.19/1.73  tff(c_660, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_657])).
% 4.19/1.73  tff(c_663, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_32, c_660])).
% 4.19/1.73  tff(c_665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_501, c_663])).
% 4.19/1.73  tff(c_666, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 4.19/1.73  tff(c_1022, plain, (![B_557, C_559, D_558, E_556, G_561, A_560]: (r1_tmap_1(D_558, B_557, k3_tmap_1(A_560, B_557, C_559, D_558, E_556), G_561) | ~r1_tmap_1(C_559, B_557, E_556, G_561) | ~m1_pre_topc(D_558, C_559) | ~m1_subset_1(G_561, u1_struct_0(D_558)) | ~m1_subset_1(G_561, u1_struct_0(C_559)) | ~m1_subset_1(E_556, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_559), u1_struct_0(B_557)))) | ~v1_funct_2(E_556, u1_struct_0(C_559), u1_struct_0(B_557)) | ~v1_funct_1(E_556) | ~m1_pre_topc(D_558, A_560) | v2_struct_0(D_558) | ~m1_pre_topc(C_559, A_560) | v2_struct_0(C_559) | ~l1_pre_topc(B_557) | ~v2_pre_topc(B_557) | v2_struct_0(B_557) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.19/1.73  tff(c_1024, plain, (![D_558, A_560, G_561]: (r1_tmap_1(D_558, '#skF_1', k3_tmap_1(A_560, '#skF_1', '#skF_4', D_558, '#skF_5'), G_561) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_561) | ~m1_pre_topc(D_558, '#skF_4') | ~m1_subset_1(G_561, u1_struct_0(D_558)) | ~m1_subset_1(G_561, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_558, A_560) | v2_struct_0(D_558) | ~m1_pre_topc('#skF_4', A_560) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(resolution, [status(thm)], [c_38, c_1022])).
% 4.19/1.73  tff(c_1027, plain, (![D_558, A_560, G_561]: (r1_tmap_1(D_558, '#skF_1', k3_tmap_1(A_560, '#skF_1', '#skF_4', D_558, '#skF_5'), G_561) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_561) | ~m1_pre_topc(D_558, '#skF_4') | ~m1_subset_1(G_561, u1_struct_0(D_558)) | ~m1_subset_1(G_561, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_558, A_560) | v2_struct_0(D_558) | ~m1_pre_topc('#skF_4', A_560) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_42, c_40, c_1024])).
% 4.19/1.73  tff(c_1036, plain, (![D_564, A_565, G_566]: (r1_tmap_1(D_564, '#skF_1', k3_tmap_1(A_565, '#skF_1', '#skF_4', D_564, '#skF_5'), G_566) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_566) | ~m1_pre_topc(D_564, '#skF_4') | ~m1_subset_1(G_566, u1_struct_0(D_564)) | ~m1_subset_1(G_566, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_564, A_565) | v2_struct_0(D_564) | ~m1_pre_topc('#skF_4', A_565) | ~l1_pre_topc(A_565) | ~v2_pre_topc(A_565) | v2_struct_0(A_565))), inference(negUnitSimplification, [status(thm)], [c_62, c_46, c_1027])).
% 4.19/1.73  tff(c_667, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 4.19/1.73  tff(c_1039, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1036, c_667])).
% 4.19/1.73  tff(c_1042, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_44, c_48, c_30, c_74, c_32, c_666, c_1039])).
% 4.19/1.73  tff(c_1044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_1042])).
% 4.19/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.73  
% 4.19/1.73  Inference rules
% 4.19/1.73  ----------------------
% 4.19/1.73  #Ref     : 0
% 4.19/1.73  #Sup     : 184
% 4.19/1.73  #Fact    : 0
% 4.19/1.73  #Define  : 0
% 4.19/1.73  #Split   : 7
% 4.19/1.73  #Chain   : 0
% 4.19/1.73  #Close   : 0
% 4.19/1.73  
% 4.19/1.73  Ordering : KBO
% 4.19/1.73  
% 4.19/1.73  Simplification rules
% 4.19/1.73  ----------------------
% 4.19/1.73  #Subsume      : 70
% 4.19/1.73  #Demod        : 237
% 4.19/1.73  #Tautology    : 38
% 4.19/1.73  #SimpNegUnit  : 7
% 4.19/1.73  #BackRed      : 0
% 4.19/1.73  
% 4.19/1.73  #Partial instantiations: 0
% 4.19/1.73  #Strategies tried      : 1
% 4.19/1.73  
% 4.19/1.73  Timing (in seconds)
% 4.19/1.73  ----------------------
% 4.19/1.73  Preprocessing        : 0.42
% 4.19/1.73  Parsing              : 0.20
% 4.19/1.73  CNF conversion       : 0.07
% 4.19/1.73  Main loop            : 0.50
% 4.19/1.73  Inferencing          : 0.17
% 4.19/1.73  Reduction            : 0.16
% 4.19/1.73  Demodulation         : 0.11
% 4.19/1.73  BG Simplification    : 0.03
% 4.19/1.73  Subsumption          : 0.12
% 4.19/1.73  Abstraction          : 0.02
% 4.19/1.73  MUC search           : 0.00
% 4.19/1.73  Cooper               : 0.00
% 4.19/1.73  Total                : 1.00
% 4.19/1.73  Index Insertion      : 0.00
% 4.19/1.73  Index Deletion       : 0.00
% 4.19/1.73  Index Matching       : 0.00
% 4.19/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
