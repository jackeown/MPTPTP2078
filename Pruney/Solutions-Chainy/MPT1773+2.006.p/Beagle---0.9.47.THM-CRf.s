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
% DateTime   : Thu Dec  3 10:27:22 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 482 expanded)
%              Number of leaves         :   38 ( 200 expanded)
%              Depth                    :   18
%              Number of atoms          :  517 (4108 expanded)
%              Number of equality atoms :   40 ( 201 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_255,negated_conjecture,(
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
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,D)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,B,E,G)
                                        <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

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

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_138,axiom,(
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

tff(f_106,axiom,(
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

tff(f_185,axiom,(
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
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_26,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_24,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_28,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_76,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_75,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_100,plain,(
    ! [B_458,A_459] :
      ( v2_pre_topc(B_458)
      | ~ m1_pre_topc(B_458,A_459)
      | ~ l1_pre_topc(A_459)
      | ~ v2_pre_topc(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_106,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_100])).

tff(c_115,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_106])).

tff(c_81,plain,(
    ! [B_456,A_457] :
      ( l1_pre_topc(B_456)
      | ~ m1_pre_topc(B_456,A_457)
      | ~ l1_pre_topc(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_96,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_87])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_30,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_8,plain,(
    ! [B_15,D_21,C_19,A_7] :
      ( k1_tops_1(B_15,D_21) = D_21
      | ~ v3_pre_topc(D_21,B_15)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(u1_struct_0(B_15)))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(B_15)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_225,plain,(
    ! [C_472,A_473] :
      ( ~ m1_subset_1(C_472,k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ l1_pre_topc(A_473)
      | ~ v2_pre_topc(A_473) ) ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_228,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_225])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_96,c_228])).

tff(c_234,plain,(
    ! [B_474,D_475] :
      ( k1_tops_1(B_474,D_475) = D_475
      | ~ v3_pre_topc(D_475,B_474)
      | ~ m1_subset_1(D_475,k1_zfmisc_1(u1_struct_0(B_474)))
      | ~ l1_pre_topc(B_474) ) ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_237,plain,
    ( k1_tops_1('#skF_4','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_234])).

tff(c_240,plain,(
    k1_tops_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_30,c_237])).

tff(c_275,plain,(
    ! [C_484,A_485,B_486] :
      ( m1_connsp_2(C_484,A_485,B_486)
      | ~ r2_hidden(B_486,k1_tops_1(A_485,C_484))
      | ~ m1_subset_1(C_484,k1_zfmisc_1(u1_struct_0(A_485)))
      | ~ m1_subset_1(B_486,u1_struct_0(A_485))
      | ~ l1_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_277,plain,(
    ! [B_486] :
      ( m1_connsp_2('#skF_6','#skF_4',B_486)
      | ~ r2_hidden(B_486,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_486,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_275])).

tff(c_279,plain,(
    ! [B_486] :
      ( m1_connsp_2('#skF_6','#skF_4',B_486)
      | ~ r2_hidden(B_486,'#skF_6')
      | ~ m1_subset_1(B_486,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_96,c_36,c_277])).

tff(c_281,plain,(
    ! [B_487] :
      ( m1_connsp_2('#skF_6','#skF_4',B_487)
      | ~ r2_hidden(B_487,'#skF_6')
      | ~ m1_subset_1(B_487,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_279])).

tff(c_284,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_75,c_281])).

tff(c_287,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_284])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_121,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_304,plain,(
    ! [C_497,E_494,B_493,D_495,A_496] :
      ( k3_tmap_1(A_496,B_493,C_497,D_495,E_494) = k2_partfun1(u1_struct_0(C_497),u1_struct_0(B_493),E_494,u1_struct_0(D_495))
      | ~ m1_pre_topc(D_495,C_497)
      | ~ m1_subset_1(E_494,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_497),u1_struct_0(B_493))))
      | ~ v1_funct_2(E_494,u1_struct_0(C_497),u1_struct_0(B_493))
      | ~ v1_funct_1(E_494)
      | ~ m1_pre_topc(D_495,A_496)
      | ~ m1_pre_topc(C_497,A_496)
      | ~ l1_pre_topc(B_493)
      | ~ v2_pre_topc(B_493)
      | v2_struct_0(B_493)
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_306,plain,(
    ! [A_496,D_495] :
      ( k3_tmap_1(A_496,'#skF_2','#skF_4',D_495,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_495))
      | ~ m1_pre_topc(D_495,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_495,A_496)
      | ~ m1_pre_topc('#skF_4',A_496)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(resolution,[status(thm)],[c_40,c_304])).

tff(c_309,plain,(
    ! [A_496,D_495] :
      ( k3_tmap_1(A_496,'#skF_2','#skF_4',D_495,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_495))
      | ~ m1_pre_topc(D_495,'#skF_4')
      | ~ m1_pre_topc(D_495,A_496)
      | ~ m1_pre_topc('#skF_4',A_496)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_306])).

tff(c_318,plain,(
    ! [A_504,D_505] :
      ( k3_tmap_1(A_504,'#skF_2','#skF_4',D_505,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_505))
      | ~ m1_pre_topc(D_505,'#skF_4')
      | ~ m1_pre_topc(D_505,A_504)
      | ~ m1_pre_topc('#skF_4',A_504)
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_309])).

tff(c_324,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_318])).

tff(c_337,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_38,c_324])).

tff(c_338,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_337])).

tff(c_288,plain,(
    ! [A_488,B_489,C_490,D_491] :
      ( k2_partfun1(u1_struct_0(A_488),u1_struct_0(B_489),C_490,u1_struct_0(D_491)) = k2_tmap_1(A_488,B_489,C_490,D_491)
      | ~ m1_pre_topc(D_491,A_488)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_488),u1_struct_0(B_489))))
      | ~ v1_funct_2(C_490,u1_struct_0(A_488),u1_struct_0(B_489))
      | ~ v1_funct_1(C_490)
      | ~ l1_pre_topc(B_489)
      | ~ v2_pre_topc(B_489)
      | v2_struct_0(B_489)
      | ~ l1_pre_topc(A_488)
      | ~ v2_pre_topc(A_488)
      | v2_struct_0(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_290,plain,(
    ! [D_491] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_491)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_491)
      | ~ m1_pre_topc(D_491,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_288])).

tff(c_293,plain,(
    ! [D_491] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_491)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_491)
      | ~ m1_pre_topc(D_491,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_96,c_56,c_54,c_44,c_42,c_290])).

tff(c_294,plain,(
    ! [D_491] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_491)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_491)
      | ~ m1_pre_topc(D_491,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_58,c_293])).

tff(c_350,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_294])).

tff(c_357,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_350])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_73,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_72])).

tff(c_161,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_73])).

tff(c_362,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_161])).

tff(c_386,plain,(
    ! [A_507,B_511,G_510,E_509,C_508,D_506] :
      ( r1_tmap_1(B_511,A_507,C_508,G_510)
      | ~ r1_tmap_1(D_506,A_507,k2_tmap_1(B_511,A_507,C_508,D_506),G_510)
      | ~ m1_connsp_2(E_509,B_511,G_510)
      | ~ r1_tarski(E_509,u1_struct_0(D_506))
      | ~ m1_subset_1(G_510,u1_struct_0(D_506))
      | ~ m1_subset_1(G_510,u1_struct_0(B_511))
      | ~ m1_subset_1(E_509,k1_zfmisc_1(u1_struct_0(B_511)))
      | ~ m1_pre_topc(D_506,B_511)
      | v2_struct_0(D_506)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_511),u1_struct_0(A_507))))
      | ~ v1_funct_2(C_508,u1_struct_0(B_511),u1_struct_0(A_507))
      | ~ v1_funct_1(C_508)
      | ~ l1_pre_topc(B_511)
      | ~ v2_pre_topc(B_511)
      | v2_struct_0(B_511)
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_388,plain,(
    ! [E_509] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_509,'#skF_4','#skF_8')
      | ~ r1_tarski(E_509,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_509,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_362,c_386])).

tff(c_391,plain,(
    ! [E_509] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_509,'#skF_4','#skF_8')
      | ~ r1_tarski(E_509,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_509,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_115,c_96,c_44,c_42,c_40,c_38,c_75,c_32,c_388])).

tff(c_393,plain,(
    ! [E_512] :
      ( ~ m1_connsp_2(E_512,'#skF_4','#skF_8')
      | ~ r1_tarski(E_512,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_512,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_48,c_52,c_121,c_391])).

tff(c_396,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_393])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_287,c_396])).

tff(c_402,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_471,plain,(
    ! [C_521,A_522] :
      ( ~ m1_subset_1(C_521,k1_zfmisc_1(u1_struct_0(A_522)))
      | ~ l1_pre_topc(A_522)
      | ~ v2_pre_topc(A_522) ) ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_474,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_471])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_96,c_474])).

tff(c_480,plain,(
    ! [B_523,D_524] :
      ( k1_tops_1(B_523,D_524) = D_524
      | ~ v3_pre_topc(D_524,B_523)
      | ~ m1_subset_1(D_524,k1_zfmisc_1(u1_struct_0(B_523)))
      | ~ l1_pre_topc(B_523) ) ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_483,plain,
    ( k1_tops_1('#skF_4','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_480])).

tff(c_486,plain,(
    k1_tops_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_30,c_483])).

tff(c_547,plain,(
    ! [C_535,A_536,B_537] :
      ( m1_connsp_2(C_535,A_536,B_537)
      | ~ r2_hidden(B_537,k1_tops_1(A_536,C_535))
      | ~ m1_subset_1(C_535,k1_zfmisc_1(u1_struct_0(A_536)))
      | ~ m1_subset_1(B_537,u1_struct_0(A_536))
      | ~ l1_pre_topc(A_536)
      | ~ v2_pre_topc(A_536)
      | v2_struct_0(A_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_549,plain,(
    ! [B_537] :
      ( m1_connsp_2('#skF_6','#skF_4',B_537)
      | ~ r2_hidden(B_537,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_537,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_547])).

tff(c_551,plain,(
    ! [B_537] :
      ( m1_connsp_2('#skF_6','#skF_4',B_537)
      | ~ r2_hidden(B_537,'#skF_6')
      | ~ m1_subset_1(B_537,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_96,c_36,c_549])).

tff(c_553,plain,(
    ! [B_538] :
      ( m1_connsp_2('#skF_6','#skF_4',B_538)
      | ~ r2_hidden(B_538,'#skF_6')
      | ~ m1_subset_1(B_538,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_551])).

tff(c_556,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_75,c_553])).

tff(c_559,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_556])).

tff(c_663,plain,(
    ! [B_563,E_561,D_558,A_559,G_562,C_560] :
      ( r1_tmap_1(D_558,A_559,k2_tmap_1(B_563,A_559,C_560,D_558),G_562)
      | ~ r1_tmap_1(B_563,A_559,C_560,G_562)
      | ~ m1_connsp_2(E_561,B_563,G_562)
      | ~ r1_tarski(E_561,u1_struct_0(D_558))
      | ~ m1_subset_1(G_562,u1_struct_0(D_558))
      | ~ m1_subset_1(G_562,u1_struct_0(B_563))
      | ~ m1_subset_1(E_561,k1_zfmisc_1(u1_struct_0(B_563)))
      | ~ m1_pre_topc(D_558,B_563)
      | v2_struct_0(D_558)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_563),u1_struct_0(A_559))))
      | ~ v1_funct_2(C_560,u1_struct_0(B_563),u1_struct_0(A_559))
      | ~ v1_funct_1(C_560)
      | ~ l1_pre_topc(B_563)
      | ~ v2_pre_topc(B_563)
      | v2_struct_0(B_563)
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559)
      | v2_struct_0(A_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_665,plain,(
    ! [D_558,A_559,C_560] :
      ( r1_tmap_1(D_558,A_559,k2_tmap_1('#skF_4',A_559,C_560,D_558),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_559,C_560,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_558))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_558))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(D_558,'#skF_4')
      | v2_struct_0(D_558)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_559))))
      | ~ v1_funct_2(C_560,u1_struct_0('#skF_4'),u1_struct_0(A_559))
      | ~ v1_funct_1(C_560)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559)
      | v2_struct_0(A_559) ) ),
    inference(resolution,[status(thm)],[c_559,c_663])).

tff(c_668,plain,(
    ! [D_558,A_559,C_560] :
      ( r1_tmap_1(D_558,A_559,k2_tmap_1('#skF_4',A_559,C_560,D_558),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_559,C_560,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_558))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_558))
      | ~ m1_pre_topc(D_558,'#skF_4')
      | v2_struct_0(D_558)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_559))))
      | ~ v1_funct_2(C_560,u1_struct_0('#skF_4'),u1_struct_0(A_559))
      | ~ v1_funct_1(C_560)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559)
      | v2_struct_0(A_559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_96,c_36,c_75,c_665])).

tff(c_670,plain,(
    ! [D_564,A_565,C_566] :
      ( r1_tmap_1(D_564,A_565,k2_tmap_1('#skF_4',A_565,C_566,D_564),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_565,C_566,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_564))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_564))
      | ~ m1_pre_topc(D_564,'#skF_4')
      | v2_struct_0(D_564)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_565))))
      | ~ v1_funct_2(C_566,u1_struct_0('#skF_4'),u1_struct_0(A_565))
      | ~ v1_funct_1(C_566)
      | ~ l1_pre_topc(A_565)
      | ~ v2_pre_topc(A_565)
      | v2_struct_0(A_565) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_668])).

tff(c_672,plain,(
    ! [D_564] :
      ( r1_tmap_1(D_564,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_564),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_564))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_564))
      | ~ m1_pre_topc(D_564,'#skF_4')
      | v2_struct_0(D_564)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_670])).

tff(c_675,plain,(
    ! [D_564] :
      ( r1_tmap_1(D_564,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_564),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_564))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_564))
      | ~ m1_pre_topc(D_564,'#skF_4')
      | v2_struct_0(D_564)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_402,c_672])).

tff(c_677,plain,(
    ! [D_567] :
      ( r1_tmap_1(D_567,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_567),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_567))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_567))
      | ~ m1_pre_topc(D_567,'#skF_4')
      | v2_struct_0(D_567) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_675])).

tff(c_576,plain,(
    ! [B_544,E_545,A_547,C_548,D_546] :
      ( k3_tmap_1(A_547,B_544,C_548,D_546,E_545) = k2_partfun1(u1_struct_0(C_548),u1_struct_0(B_544),E_545,u1_struct_0(D_546))
      | ~ m1_pre_topc(D_546,C_548)
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_548),u1_struct_0(B_544))))
      | ~ v1_funct_2(E_545,u1_struct_0(C_548),u1_struct_0(B_544))
      | ~ v1_funct_1(E_545)
      | ~ m1_pre_topc(D_546,A_547)
      | ~ m1_pre_topc(C_548,A_547)
      | ~ l1_pre_topc(B_544)
      | ~ v2_pre_topc(B_544)
      | v2_struct_0(B_544)
      | ~ l1_pre_topc(A_547)
      | ~ v2_pre_topc(A_547)
      | v2_struct_0(A_547) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_578,plain,(
    ! [A_547,D_546] :
      ( k3_tmap_1(A_547,'#skF_2','#skF_4',D_546,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_546))
      | ~ m1_pre_topc(D_546,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_546,A_547)
      | ~ m1_pre_topc('#skF_4',A_547)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_547)
      | ~ v2_pre_topc(A_547)
      | v2_struct_0(A_547) ) ),
    inference(resolution,[status(thm)],[c_40,c_576])).

tff(c_581,plain,(
    ! [A_547,D_546] :
      ( k3_tmap_1(A_547,'#skF_2','#skF_4',D_546,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_546))
      | ~ m1_pre_topc(D_546,'#skF_4')
      | ~ m1_pre_topc(D_546,A_547)
      | ~ m1_pre_topc('#skF_4',A_547)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_547)
      | ~ v2_pre_topc(A_547)
      | v2_struct_0(A_547) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_578])).

tff(c_583,plain,(
    ! [A_549,D_550] :
      ( k3_tmap_1(A_549,'#skF_2','#skF_4',D_550,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_550))
      | ~ m1_pre_topc(D_550,'#skF_4')
      | ~ m1_pre_topc(D_550,A_549)
      | ~ m1_pre_topc('#skF_4',A_549)
      | ~ l1_pre_topc(A_549)
      | ~ v2_pre_topc(A_549)
      | v2_struct_0(A_549) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_581])).

tff(c_589,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_583])).

tff(c_602,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_38,c_589])).

tff(c_603,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_602])).

tff(c_560,plain,(
    ! [A_539,B_540,C_541,D_542] :
      ( k2_partfun1(u1_struct_0(A_539),u1_struct_0(B_540),C_541,u1_struct_0(D_542)) = k2_tmap_1(A_539,B_540,C_541,D_542)
      | ~ m1_pre_topc(D_542,A_539)
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_539),u1_struct_0(B_540))))
      | ~ v1_funct_2(C_541,u1_struct_0(A_539),u1_struct_0(B_540))
      | ~ v1_funct_1(C_541)
      | ~ l1_pre_topc(B_540)
      | ~ v2_pre_topc(B_540)
      | v2_struct_0(B_540)
      | ~ l1_pre_topc(A_539)
      | ~ v2_pre_topc(A_539)
      | v2_struct_0(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_562,plain,(
    ! [D_542] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_542)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_542)
      | ~ m1_pre_topc(D_542,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_560])).

tff(c_565,plain,(
    ! [D_542] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_542)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_542)
      | ~ m1_pre_topc(D_542,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_96,c_56,c_54,c_44,c_42,c_562])).

tff(c_566,plain,(
    ! [D_542] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_542)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_542)
      | ~ m1_pre_topc(D_542,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_58,c_565])).

tff(c_615,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_566])).

tff(c_622,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_615])).

tff(c_401,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_627,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_401])).

tff(c_682,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_677,c_627])).

tff(c_689,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_26,c_682])).

tff(c_691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.56  
% 3.71/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.56  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.71/1.56  
% 3.71/1.56  %Foreground sorts:
% 3.71/1.56  
% 3.71/1.56  
% 3.71/1.56  %Background operators:
% 3.71/1.56  
% 3.71/1.56  
% 3.71/1.56  %Foreground operators:
% 3.71/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.71/1.56  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.71/1.56  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.71/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.71/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.71/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.71/1.56  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.71/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.71/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.71/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.71/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.71/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.71/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.71/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.71/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.71/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.71/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.71/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.71/1.56  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.71/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.71/1.56  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.71/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.71/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.56  
% 3.71/1.59  tff(f_255, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.71/1.59  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.71/1.59  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.71/1.59  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 3.71/1.59  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.71/1.59  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.71/1.59  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.71/1.59  tff(f_185, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.71/1.59  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_32, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_26, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_42, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_24, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_28, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_76, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 3.71/1.59  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_75, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34])).
% 3.71/1.59  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_100, plain, (![B_458, A_459]: (v2_pre_topc(B_458) | ~m1_pre_topc(B_458, A_459) | ~l1_pre_topc(A_459) | ~v2_pre_topc(A_459))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.71/1.59  tff(c_106, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_100])).
% 3.71/1.59  tff(c_115, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_106])).
% 3.71/1.59  tff(c_81, plain, (![B_456, A_457]: (l1_pre_topc(B_456) | ~m1_pre_topc(B_456, A_457) | ~l1_pre_topc(A_457))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.71/1.59  tff(c_87, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_81])).
% 3.71/1.59  tff(c_96, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_87])).
% 3.71/1.59  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_30, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_8, plain, (![B_15, D_21, C_19, A_7]: (k1_tops_1(B_15, D_21)=D_21 | ~v3_pre_topc(D_21, B_15) | ~m1_subset_1(D_21, k1_zfmisc_1(u1_struct_0(B_15))) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(B_15) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.71/1.59  tff(c_225, plain, (![C_472, A_473]: (~m1_subset_1(C_472, k1_zfmisc_1(u1_struct_0(A_473))) | ~l1_pre_topc(A_473) | ~v2_pre_topc(A_473))), inference(splitLeft, [status(thm)], [c_8])).
% 3.71/1.59  tff(c_228, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_225])).
% 3.71/1.59  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_96, c_228])).
% 3.71/1.59  tff(c_234, plain, (![B_474, D_475]: (k1_tops_1(B_474, D_475)=D_475 | ~v3_pre_topc(D_475, B_474) | ~m1_subset_1(D_475, k1_zfmisc_1(u1_struct_0(B_474))) | ~l1_pre_topc(B_474))), inference(splitRight, [status(thm)], [c_8])).
% 3.71/1.59  tff(c_237, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_234])).
% 3.71/1.59  tff(c_240, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_30, c_237])).
% 3.71/1.59  tff(c_275, plain, (![C_484, A_485, B_486]: (m1_connsp_2(C_484, A_485, B_486) | ~r2_hidden(B_486, k1_tops_1(A_485, C_484)) | ~m1_subset_1(C_484, k1_zfmisc_1(u1_struct_0(A_485))) | ~m1_subset_1(B_486, u1_struct_0(A_485)) | ~l1_pre_topc(A_485) | ~v2_pre_topc(A_485) | v2_struct_0(A_485))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.71/1.59  tff(c_277, plain, (![B_486]: (m1_connsp_2('#skF_6', '#skF_4', B_486) | ~r2_hidden(B_486, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_486, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_240, c_275])).
% 3.71/1.59  tff(c_279, plain, (![B_486]: (m1_connsp_2('#skF_6', '#skF_4', B_486) | ~r2_hidden(B_486, '#skF_6') | ~m1_subset_1(B_486, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_96, c_36, c_277])).
% 3.71/1.59  tff(c_281, plain, (![B_487]: (m1_connsp_2('#skF_6', '#skF_4', B_487) | ~r2_hidden(B_487, '#skF_6') | ~m1_subset_1(B_487, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_279])).
% 3.71/1.59  tff(c_284, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_75, c_281])).
% 3.71/1.59  tff(c_287, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_284])).
% 3.71/1.59  tff(c_66, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_74, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 3.71/1.59  tff(c_121, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_74])).
% 3.71/1.59  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_304, plain, (![C_497, E_494, B_493, D_495, A_496]: (k3_tmap_1(A_496, B_493, C_497, D_495, E_494)=k2_partfun1(u1_struct_0(C_497), u1_struct_0(B_493), E_494, u1_struct_0(D_495)) | ~m1_pre_topc(D_495, C_497) | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_497), u1_struct_0(B_493)))) | ~v1_funct_2(E_494, u1_struct_0(C_497), u1_struct_0(B_493)) | ~v1_funct_1(E_494) | ~m1_pre_topc(D_495, A_496) | ~m1_pre_topc(C_497, A_496) | ~l1_pre_topc(B_493) | ~v2_pre_topc(B_493) | v2_struct_0(B_493) | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.71/1.59  tff(c_306, plain, (![A_496, D_495]: (k3_tmap_1(A_496, '#skF_2', '#skF_4', D_495, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_495)) | ~m1_pre_topc(D_495, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_495, A_496) | ~m1_pre_topc('#skF_4', A_496) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(resolution, [status(thm)], [c_40, c_304])).
% 3.71/1.59  tff(c_309, plain, (![A_496, D_495]: (k3_tmap_1(A_496, '#skF_2', '#skF_4', D_495, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_495)) | ~m1_pre_topc(D_495, '#skF_4') | ~m1_pre_topc(D_495, A_496) | ~m1_pre_topc('#skF_4', A_496) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_306])).
% 3.71/1.59  tff(c_318, plain, (![A_504, D_505]: (k3_tmap_1(A_504, '#skF_2', '#skF_4', D_505, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_505)) | ~m1_pre_topc(D_505, '#skF_4') | ~m1_pre_topc(D_505, A_504) | ~m1_pre_topc('#skF_4', A_504) | ~l1_pre_topc(A_504) | ~v2_pre_topc(A_504) | v2_struct_0(A_504))), inference(negUnitSimplification, [status(thm)], [c_58, c_309])).
% 3.71/1.59  tff(c_324, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_318])).
% 3.71/1.59  tff(c_337, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_38, c_324])).
% 3.71/1.59  tff(c_338, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_337])).
% 3.71/1.59  tff(c_288, plain, (![A_488, B_489, C_490, D_491]: (k2_partfun1(u1_struct_0(A_488), u1_struct_0(B_489), C_490, u1_struct_0(D_491))=k2_tmap_1(A_488, B_489, C_490, D_491) | ~m1_pre_topc(D_491, A_488) | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_488), u1_struct_0(B_489)))) | ~v1_funct_2(C_490, u1_struct_0(A_488), u1_struct_0(B_489)) | ~v1_funct_1(C_490) | ~l1_pre_topc(B_489) | ~v2_pre_topc(B_489) | v2_struct_0(B_489) | ~l1_pre_topc(A_488) | ~v2_pre_topc(A_488) | v2_struct_0(A_488))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.71/1.59  tff(c_290, plain, (![D_491]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_491))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_491) | ~m1_pre_topc(D_491, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_288])).
% 3.71/1.59  tff(c_293, plain, (![D_491]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_491))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_491) | ~m1_pre_topc(D_491, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_96, c_56, c_54, c_44, c_42, c_290])).
% 3.71/1.59  tff(c_294, plain, (![D_491]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_491))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_491) | ~m1_pre_topc(D_491, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_58, c_293])).
% 3.71/1.59  tff(c_350, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_338, c_294])).
% 3.71/1.59  tff(c_357, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_350])).
% 3.71/1.59  tff(c_72, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.71/1.59  tff(c_73, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_72])).
% 3.71/1.59  tff(c_161, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_121, c_73])).
% 3.71/1.59  tff(c_362, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_161])).
% 3.71/1.59  tff(c_386, plain, (![A_507, B_511, G_510, E_509, C_508, D_506]: (r1_tmap_1(B_511, A_507, C_508, G_510) | ~r1_tmap_1(D_506, A_507, k2_tmap_1(B_511, A_507, C_508, D_506), G_510) | ~m1_connsp_2(E_509, B_511, G_510) | ~r1_tarski(E_509, u1_struct_0(D_506)) | ~m1_subset_1(G_510, u1_struct_0(D_506)) | ~m1_subset_1(G_510, u1_struct_0(B_511)) | ~m1_subset_1(E_509, k1_zfmisc_1(u1_struct_0(B_511))) | ~m1_pre_topc(D_506, B_511) | v2_struct_0(D_506) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_511), u1_struct_0(A_507)))) | ~v1_funct_2(C_508, u1_struct_0(B_511), u1_struct_0(A_507)) | ~v1_funct_1(C_508) | ~l1_pre_topc(B_511) | ~v2_pre_topc(B_511) | v2_struct_0(B_511) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.71/1.59  tff(c_388, plain, (![E_509]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_509, '#skF_4', '#skF_8') | ~r1_tarski(E_509, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_509, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_362, c_386])).
% 3.71/1.59  tff(c_391, plain, (![E_509]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_509, '#skF_4', '#skF_8') | ~r1_tarski(E_509, u1_struct_0('#skF_3')) | ~m1_subset_1(E_509, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_115, c_96, c_44, c_42, c_40, c_38, c_75, c_32, c_388])).
% 3.71/1.59  tff(c_393, plain, (![E_512]: (~m1_connsp_2(E_512, '#skF_4', '#skF_8') | ~r1_tarski(E_512, u1_struct_0('#skF_3')) | ~m1_subset_1(E_512, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_48, c_52, c_121, c_391])).
% 3.71/1.59  tff(c_396, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_393])).
% 3.71/1.59  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_287, c_396])).
% 3.71/1.59  tff(c_402, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_74])).
% 3.71/1.59  tff(c_471, plain, (![C_521, A_522]: (~m1_subset_1(C_521, k1_zfmisc_1(u1_struct_0(A_522))) | ~l1_pre_topc(A_522) | ~v2_pre_topc(A_522))), inference(splitLeft, [status(thm)], [c_8])).
% 3.71/1.59  tff(c_474, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_471])).
% 3.71/1.59  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_96, c_474])).
% 3.71/1.59  tff(c_480, plain, (![B_523, D_524]: (k1_tops_1(B_523, D_524)=D_524 | ~v3_pre_topc(D_524, B_523) | ~m1_subset_1(D_524, k1_zfmisc_1(u1_struct_0(B_523))) | ~l1_pre_topc(B_523))), inference(splitRight, [status(thm)], [c_8])).
% 3.71/1.59  tff(c_483, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_480])).
% 3.71/1.59  tff(c_486, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_30, c_483])).
% 3.71/1.59  tff(c_547, plain, (![C_535, A_536, B_537]: (m1_connsp_2(C_535, A_536, B_537) | ~r2_hidden(B_537, k1_tops_1(A_536, C_535)) | ~m1_subset_1(C_535, k1_zfmisc_1(u1_struct_0(A_536))) | ~m1_subset_1(B_537, u1_struct_0(A_536)) | ~l1_pre_topc(A_536) | ~v2_pre_topc(A_536) | v2_struct_0(A_536))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.71/1.59  tff(c_549, plain, (![B_537]: (m1_connsp_2('#skF_6', '#skF_4', B_537) | ~r2_hidden(B_537, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_537, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_486, c_547])).
% 3.71/1.59  tff(c_551, plain, (![B_537]: (m1_connsp_2('#skF_6', '#skF_4', B_537) | ~r2_hidden(B_537, '#skF_6') | ~m1_subset_1(B_537, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_96, c_36, c_549])).
% 3.71/1.59  tff(c_553, plain, (![B_538]: (m1_connsp_2('#skF_6', '#skF_4', B_538) | ~r2_hidden(B_538, '#skF_6') | ~m1_subset_1(B_538, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_551])).
% 3.71/1.59  tff(c_556, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_75, c_553])).
% 3.71/1.59  tff(c_559, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_556])).
% 3.71/1.59  tff(c_663, plain, (![B_563, E_561, D_558, A_559, G_562, C_560]: (r1_tmap_1(D_558, A_559, k2_tmap_1(B_563, A_559, C_560, D_558), G_562) | ~r1_tmap_1(B_563, A_559, C_560, G_562) | ~m1_connsp_2(E_561, B_563, G_562) | ~r1_tarski(E_561, u1_struct_0(D_558)) | ~m1_subset_1(G_562, u1_struct_0(D_558)) | ~m1_subset_1(G_562, u1_struct_0(B_563)) | ~m1_subset_1(E_561, k1_zfmisc_1(u1_struct_0(B_563))) | ~m1_pre_topc(D_558, B_563) | v2_struct_0(D_558) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_563), u1_struct_0(A_559)))) | ~v1_funct_2(C_560, u1_struct_0(B_563), u1_struct_0(A_559)) | ~v1_funct_1(C_560) | ~l1_pre_topc(B_563) | ~v2_pre_topc(B_563) | v2_struct_0(B_563) | ~l1_pre_topc(A_559) | ~v2_pre_topc(A_559) | v2_struct_0(A_559))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.71/1.59  tff(c_665, plain, (![D_558, A_559, C_560]: (r1_tmap_1(D_558, A_559, k2_tmap_1('#skF_4', A_559, C_560, D_558), '#skF_8') | ~r1_tmap_1('#skF_4', A_559, C_560, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_558)) | ~m1_subset_1('#skF_8', u1_struct_0(D_558)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(D_558, '#skF_4') | v2_struct_0(D_558) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_559)))) | ~v1_funct_2(C_560, u1_struct_0('#skF_4'), u1_struct_0(A_559)) | ~v1_funct_1(C_560) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_559) | ~v2_pre_topc(A_559) | v2_struct_0(A_559))), inference(resolution, [status(thm)], [c_559, c_663])).
% 3.71/1.59  tff(c_668, plain, (![D_558, A_559, C_560]: (r1_tmap_1(D_558, A_559, k2_tmap_1('#skF_4', A_559, C_560, D_558), '#skF_8') | ~r1_tmap_1('#skF_4', A_559, C_560, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_558)) | ~m1_subset_1('#skF_8', u1_struct_0(D_558)) | ~m1_pre_topc(D_558, '#skF_4') | v2_struct_0(D_558) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_559)))) | ~v1_funct_2(C_560, u1_struct_0('#skF_4'), u1_struct_0(A_559)) | ~v1_funct_1(C_560) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_559) | ~v2_pre_topc(A_559) | v2_struct_0(A_559))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_96, c_36, c_75, c_665])).
% 3.71/1.59  tff(c_670, plain, (![D_564, A_565, C_566]: (r1_tmap_1(D_564, A_565, k2_tmap_1('#skF_4', A_565, C_566, D_564), '#skF_8') | ~r1_tmap_1('#skF_4', A_565, C_566, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_564)) | ~m1_subset_1('#skF_8', u1_struct_0(D_564)) | ~m1_pre_topc(D_564, '#skF_4') | v2_struct_0(D_564) | ~m1_subset_1(C_566, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_565)))) | ~v1_funct_2(C_566, u1_struct_0('#skF_4'), u1_struct_0(A_565)) | ~v1_funct_1(C_566) | ~l1_pre_topc(A_565) | ~v2_pre_topc(A_565) | v2_struct_0(A_565))), inference(negUnitSimplification, [status(thm)], [c_48, c_668])).
% 3.71/1.59  tff(c_672, plain, (![D_564]: (r1_tmap_1(D_564, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_564), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_564)) | ~m1_subset_1('#skF_8', u1_struct_0(D_564)) | ~m1_pre_topc(D_564, '#skF_4') | v2_struct_0(D_564) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_670])).
% 3.71/1.59  tff(c_675, plain, (![D_564]: (r1_tmap_1(D_564, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_564), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_564)) | ~m1_subset_1('#skF_8', u1_struct_0(D_564)) | ~m1_pre_topc(D_564, '#skF_4') | v2_struct_0(D_564) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_402, c_672])).
% 3.71/1.59  tff(c_677, plain, (![D_567]: (r1_tmap_1(D_567, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_567), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_567)) | ~m1_subset_1('#skF_8', u1_struct_0(D_567)) | ~m1_pre_topc(D_567, '#skF_4') | v2_struct_0(D_567))), inference(negUnitSimplification, [status(thm)], [c_58, c_675])).
% 3.71/1.59  tff(c_576, plain, (![B_544, E_545, A_547, C_548, D_546]: (k3_tmap_1(A_547, B_544, C_548, D_546, E_545)=k2_partfun1(u1_struct_0(C_548), u1_struct_0(B_544), E_545, u1_struct_0(D_546)) | ~m1_pre_topc(D_546, C_548) | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_548), u1_struct_0(B_544)))) | ~v1_funct_2(E_545, u1_struct_0(C_548), u1_struct_0(B_544)) | ~v1_funct_1(E_545) | ~m1_pre_topc(D_546, A_547) | ~m1_pre_topc(C_548, A_547) | ~l1_pre_topc(B_544) | ~v2_pre_topc(B_544) | v2_struct_0(B_544) | ~l1_pre_topc(A_547) | ~v2_pre_topc(A_547) | v2_struct_0(A_547))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.71/1.59  tff(c_578, plain, (![A_547, D_546]: (k3_tmap_1(A_547, '#skF_2', '#skF_4', D_546, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_546)) | ~m1_pre_topc(D_546, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_546, A_547) | ~m1_pre_topc('#skF_4', A_547) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_547) | ~v2_pre_topc(A_547) | v2_struct_0(A_547))), inference(resolution, [status(thm)], [c_40, c_576])).
% 3.71/1.59  tff(c_581, plain, (![A_547, D_546]: (k3_tmap_1(A_547, '#skF_2', '#skF_4', D_546, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_546)) | ~m1_pre_topc(D_546, '#skF_4') | ~m1_pre_topc(D_546, A_547) | ~m1_pre_topc('#skF_4', A_547) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_547) | ~v2_pre_topc(A_547) | v2_struct_0(A_547))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_578])).
% 3.71/1.59  tff(c_583, plain, (![A_549, D_550]: (k3_tmap_1(A_549, '#skF_2', '#skF_4', D_550, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_550)) | ~m1_pre_topc(D_550, '#skF_4') | ~m1_pre_topc(D_550, A_549) | ~m1_pre_topc('#skF_4', A_549) | ~l1_pre_topc(A_549) | ~v2_pre_topc(A_549) | v2_struct_0(A_549))), inference(negUnitSimplification, [status(thm)], [c_58, c_581])).
% 3.71/1.59  tff(c_589, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_583])).
% 3.71/1.59  tff(c_602, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_38, c_589])).
% 3.71/1.59  tff(c_603, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_602])).
% 3.71/1.59  tff(c_560, plain, (![A_539, B_540, C_541, D_542]: (k2_partfun1(u1_struct_0(A_539), u1_struct_0(B_540), C_541, u1_struct_0(D_542))=k2_tmap_1(A_539, B_540, C_541, D_542) | ~m1_pre_topc(D_542, A_539) | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_539), u1_struct_0(B_540)))) | ~v1_funct_2(C_541, u1_struct_0(A_539), u1_struct_0(B_540)) | ~v1_funct_1(C_541) | ~l1_pre_topc(B_540) | ~v2_pre_topc(B_540) | v2_struct_0(B_540) | ~l1_pre_topc(A_539) | ~v2_pre_topc(A_539) | v2_struct_0(A_539))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.71/1.59  tff(c_562, plain, (![D_542]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_542))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_542) | ~m1_pre_topc(D_542, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_560])).
% 3.71/1.59  tff(c_565, plain, (![D_542]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_542))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_542) | ~m1_pre_topc(D_542, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_96, c_56, c_54, c_44, c_42, c_562])).
% 3.71/1.59  tff(c_566, plain, (![D_542]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_542))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_542) | ~m1_pre_topc(D_542, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_58, c_565])).
% 3.71/1.59  tff(c_615, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_603, c_566])).
% 3.71/1.59  tff(c_622, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_615])).
% 3.71/1.59  tff(c_401, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_74])).
% 3.71/1.59  tff(c_627, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_401])).
% 3.71/1.59  tff(c_682, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_677, c_627])).
% 3.71/1.59  tff(c_689, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_26, c_682])).
% 3.71/1.59  tff(c_691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_689])).
% 3.71/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.59  
% 3.71/1.59  Inference rules
% 3.71/1.59  ----------------------
% 3.71/1.59  #Ref     : 0
% 3.71/1.59  #Sup     : 113
% 3.71/1.59  #Fact    : 0
% 3.71/1.59  #Define  : 0
% 3.71/1.59  #Split   : 9
% 3.71/1.59  #Chain   : 0
% 3.71/1.59  #Close   : 0
% 3.71/1.59  
% 3.71/1.59  Ordering : KBO
% 3.71/1.59  
% 3.71/1.59  Simplification rules
% 3.71/1.59  ----------------------
% 3.71/1.59  #Subsume      : 13
% 3.71/1.59  #Demod        : 237
% 3.71/1.59  #Tautology    : 59
% 3.71/1.59  #SimpNegUnit  : 23
% 3.71/1.59  #BackRed      : 4
% 3.71/1.59  
% 3.71/1.59  #Partial instantiations: 0
% 3.71/1.59  #Strategies tried      : 1
% 3.71/1.59  
% 3.71/1.59  Timing (in seconds)
% 3.71/1.59  ----------------------
% 3.71/1.59  Preprocessing        : 0.43
% 3.71/1.59  Parsing              : 0.22
% 3.71/1.59  CNF conversion       : 0.06
% 3.71/1.59  Main loop            : 0.36
% 3.71/1.59  Inferencing          : 0.12
% 3.71/1.59  Reduction            : 0.12
% 3.71/1.59  Demodulation         : 0.09
% 3.71/1.59  BG Simplification    : 0.02
% 3.71/1.59  Subsumption          : 0.06
% 3.71/1.59  Abstraction          : 0.01
% 3.71/1.59  MUC search           : 0.00
% 3.71/1.59  Cooper               : 0.00
% 3.71/1.59  Total                : 0.84
% 3.71/1.59  Index Insertion      : 0.00
% 3.71/1.59  Index Deletion       : 0.00
% 3.71/1.59  Index Matching       : 0.00
% 3.71/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
