%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:22 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 316 expanded)
%              Number of leaves         :   34 ( 136 expanded)
%              Depth                    :   18
%              Number of atoms          :  380 (2666 expanded)
%              Number of equality atoms :   12 ( 121 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_146,axiom,(
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
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( r1_tarski(F,u1_struct_0(C))
                                        & m1_connsp_2(F,D,G)
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_28,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_22,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_20,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_24,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_72,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_71,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_96,plain,(
    ! [B_540,A_541] :
      ( v2_pre_topc(B_540)
      | ~ m1_pre_topc(B_540,A_541)
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_111,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_102])).

tff(c_77,plain,(
    ! [B_538,A_539] :
      ( l1_pre_topc(B_538)
      | ~ m1_pre_topc(B_538,A_539)
      | ~ l1_pre_topc(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_90,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_83])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_26,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

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

tff(c_222,plain,(
    ! [C_554,A_555] :
      ( ~ m1_subset_1(C_554,k1_zfmisc_1(u1_struct_0(A_555)))
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555) ) ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_225,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_222])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_90,c_225])).

tff(c_231,plain,(
    ! [B_556,D_557] :
      ( k1_tops_1(B_556,D_557) = D_557
      | ~ v3_pre_topc(D_557,B_556)
      | ~ m1_subset_1(D_557,k1_zfmisc_1(u1_struct_0(B_556)))
      | ~ l1_pre_topc(B_556) ) ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_234,plain,
    ( k1_tops_1('#skF_4','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_231])).

tff(c_237,plain,(
    k1_tops_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_26,c_234])).

tff(c_272,plain,(
    ! [C_566,A_567,B_568] :
      ( m1_connsp_2(C_566,A_567,B_568)
      | ~ r2_hidden(B_568,k1_tops_1(A_567,C_566))
      | ~ m1_subset_1(C_566,k1_zfmisc_1(u1_struct_0(A_567)))
      | ~ m1_subset_1(B_568,u1_struct_0(A_567))
      | ~ l1_pre_topc(A_567)
      | ~ v2_pre_topc(A_567)
      | v2_struct_0(A_567) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_274,plain,(
    ! [B_568] :
      ( m1_connsp_2('#skF_6','#skF_4',B_568)
      | ~ r2_hidden(B_568,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_568,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_272])).

tff(c_276,plain,(
    ! [B_568] :
      ( m1_connsp_2('#skF_6','#skF_4',B_568)
      | ~ r2_hidden(B_568,'#skF_6')
      | ~ m1_subset_1(B_568,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_90,c_32,c_274])).

tff(c_278,plain,(
    ! [B_569] :
      ( m1_connsp_2('#skF_6','#skF_4',B_569)
      | ~ r2_hidden(B_569,'#skF_6')
      | ~ m1_subset_1(B_569,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_276])).

tff(c_281,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_71,c_278])).

tff(c_284,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_281])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_69,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_117,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_158,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_70])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_299,plain,(
    ! [B_585,E_587,H_582,D_583,A_584,C_586,F_581] :
      ( r1_tmap_1(D_583,B_585,E_587,H_582)
      | ~ r1_tmap_1(C_586,B_585,k3_tmap_1(A_584,B_585,D_583,C_586,E_587),H_582)
      | ~ m1_connsp_2(F_581,D_583,H_582)
      | ~ r1_tarski(F_581,u1_struct_0(C_586))
      | ~ m1_subset_1(H_582,u1_struct_0(C_586))
      | ~ m1_subset_1(H_582,u1_struct_0(D_583))
      | ~ m1_subset_1(F_581,k1_zfmisc_1(u1_struct_0(D_583)))
      | ~ m1_pre_topc(C_586,D_583)
      | ~ m1_subset_1(E_587,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_583),u1_struct_0(B_585))))
      | ~ v1_funct_2(E_587,u1_struct_0(D_583),u1_struct_0(B_585))
      | ~ v1_funct_1(E_587)
      | ~ m1_pre_topc(D_583,A_584)
      | v2_struct_0(D_583)
      | ~ m1_pre_topc(C_586,A_584)
      | v2_struct_0(C_586)
      | ~ l1_pre_topc(B_585)
      | ~ v2_pre_topc(B_585)
      | v2_struct_0(B_585)
      | ~ l1_pre_topc(A_584)
      | ~ v2_pre_topc(A_584)
      | v2_struct_0(A_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_301,plain,(
    ! [F_581] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_581,'#skF_4','#skF_8')
      | ~ r1_tarski(F_581,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_581,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_117,c_299])).

tff(c_304,plain,(
    ! [F_581] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_581,'#skF_4','#skF_8')
      | ~ r1_tarski(F_581,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_581,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_46,c_42,c_40,c_38,c_36,c_34,c_71,c_28,c_301])).

tff(c_306,plain,(
    ! [F_588] :
      ( ~ m1_connsp_2(F_588,'#skF_4','#skF_8')
      | ~ r1_tarski(F_588,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_588,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_48,c_44,c_158,c_304])).

tff(c_309,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_306])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_284,c_309])).

tff(c_314,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_410,plain,(
    ! [C_599,A_600] :
      ( ~ m1_subset_1(C_599,k1_zfmisc_1(u1_struct_0(A_600)))
      | ~ l1_pre_topc(A_600)
      | ~ v2_pre_topc(A_600) ) ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_413,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_410])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_90,c_413])).

tff(c_419,plain,(
    ! [B_601,D_602] :
      ( k1_tops_1(B_601,D_602) = D_602
      | ~ v3_pre_topc(D_602,B_601)
      | ~ m1_subset_1(D_602,k1_zfmisc_1(u1_struct_0(B_601)))
      | ~ l1_pre_topc(B_601) ) ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_422,plain,
    ( k1_tops_1('#skF_4','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_419])).

tff(c_425,plain,(
    k1_tops_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_26,c_422])).

tff(c_447,plain,(
    ! [C_607,A_608,B_609] :
      ( m1_connsp_2(C_607,A_608,B_609)
      | ~ r2_hidden(B_609,k1_tops_1(A_608,C_607))
      | ~ m1_subset_1(C_607,k1_zfmisc_1(u1_struct_0(A_608)))
      | ~ m1_subset_1(B_609,u1_struct_0(A_608))
      | ~ l1_pre_topc(A_608)
      | ~ v2_pre_topc(A_608)
      | v2_struct_0(A_608) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_449,plain,(
    ! [B_609] :
      ( m1_connsp_2('#skF_6','#skF_4',B_609)
      | ~ r2_hidden(B_609,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_609,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_447])).

tff(c_451,plain,(
    ! [B_609] :
      ( m1_connsp_2('#skF_6','#skF_4',B_609)
      | ~ r2_hidden(B_609,'#skF_6')
      | ~ m1_subset_1(B_609,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_90,c_32,c_449])).

tff(c_453,plain,(
    ! [B_610] :
      ( m1_connsp_2('#skF_6','#skF_4',B_610)
      | ~ r2_hidden(B_610,'#skF_6')
      | ~ m1_subset_1(B_610,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_451])).

tff(c_456,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_71,c_453])).

tff(c_459,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_456])).

tff(c_474,plain,(
    ! [B_619,H_616,D_617,F_615,E_621,A_618,C_620] :
      ( r1_tmap_1(C_620,B_619,k3_tmap_1(A_618,B_619,D_617,C_620,E_621),H_616)
      | ~ r1_tmap_1(D_617,B_619,E_621,H_616)
      | ~ m1_connsp_2(F_615,D_617,H_616)
      | ~ r1_tarski(F_615,u1_struct_0(C_620))
      | ~ m1_subset_1(H_616,u1_struct_0(C_620))
      | ~ m1_subset_1(H_616,u1_struct_0(D_617))
      | ~ m1_subset_1(F_615,k1_zfmisc_1(u1_struct_0(D_617)))
      | ~ m1_pre_topc(C_620,D_617)
      | ~ m1_subset_1(E_621,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_617),u1_struct_0(B_619))))
      | ~ v1_funct_2(E_621,u1_struct_0(D_617),u1_struct_0(B_619))
      | ~ v1_funct_1(E_621)
      | ~ m1_pre_topc(D_617,A_618)
      | v2_struct_0(D_617)
      | ~ m1_pre_topc(C_620,A_618)
      | v2_struct_0(C_620)
      | ~ l1_pre_topc(B_619)
      | ~ v2_pre_topc(B_619)
      | v2_struct_0(B_619)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_476,plain,(
    ! [C_620,B_619,A_618,E_621] :
      ( r1_tmap_1(C_620,B_619,k3_tmap_1(A_618,B_619,'#skF_4',C_620,E_621),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_619,E_621,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_620))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_620))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(C_620,'#skF_4')
      | ~ m1_subset_1(E_621,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_619))))
      | ~ v1_funct_2(E_621,u1_struct_0('#skF_4'),u1_struct_0(B_619))
      | ~ v1_funct_1(E_621)
      | ~ m1_pre_topc('#skF_4',A_618)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_620,A_618)
      | v2_struct_0(C_620)
      | ~ l1_pre_topc(B_619)
      | ~ v2_pre_topc(B_619)
      | v2_struct_0(B_619)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(resolution,[status(thm)],[c_459,c_474])).

tff(c_479,plain,(
    ! [C_620,B_619,A_618,E_621] :
      ( r1_tmap_1(C_620,B_619,k3_tmap_1(A_618,B_619,'#skF_4',C_620,E_621),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_619,E_621,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_620))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_620))
      | ~ m1_pre_topc(C_620,'#skF_4')
      | ~ m1_subset_1(E_621,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_619))))
      | ~ v1_funct_2(E_621,u1_struct_0('#skF_4'),u1_struct_0(B_619))
      | ~ v1_funct_1(E_621)
      | ~ m1_pre_topc('#skF_4',A_618)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_620,A_618)
      | v2_struct_0(C_620)
      | ~ l1_pre_topc(B_619)
      | ~ v2_pre_topc(B_619)
      | v2_struct_0(B_619)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_71,c_476])).

tff(c_481,plain,(
    ! [C_622,B_623,A_624,E_625] :
      ( r1_tmap_1(C_622,B_623,k3_tmap_1(A_624,B_623,'#skF_4',C_622,E_625),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_623,E_625,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_622))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_622))
      | ~ m1_pre_topc(C_622,'#skF_4')
      | ~ m1_subset_1(E_625,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_623))))
      | ~ v1_funct_2(E_625,u1_struct_0('#skF_4'),u1_struct_0(B_623))
      | ~ v1_funct_1(E_625)
      | ~ m1_pre_topc('#skF_4',A_624)
      | ~ m1_pre_topc(C_622,A_624)
      | v2_struct_0(C_622)
      | ~ l1_pre_topc(B_623)
      | ~ v2_pre_topc(B_623)
      | v2_struct_0(B_623)
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_479])).

tff(c_483,plain,(
    ! [C_622,A_624] :
      ( r1_tmap_1(C_622,'#skF_2',k3_tmap_1(A_624,'#skF_2','#skF_4',C_622,'#skF_5'),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_622))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_622))
      | ~ m1_pre_topc(C_622,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_624)
      | ~ m1_pre_topc(C_622,A_624)
      | v2_struct_0(C_622)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(resolution,[status(thm)],[c_36,c_481])).

tff(c_486,plain,(
    ! [C_622,A_624] :
      ( r1_tmap_1(C_622,'#skF_2',k3_tmap_1(A_624,'#skF_2','#skF_4',C_622,'#skF_5'),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_622))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_622))
      | ~ m1_pre_topc(C_622,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_624)
      | ~ m1_pre_topc(C_622,A_624)
      | v2_struct_0(C_622)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_314,c_483])).

tff(c_488,plain,(
    ! [C_626,A_627] :
      ( r1_tmap_1(C_626,'#skF_2',k3_tmap_1(A_627,'#skF_2','#skF_4',C_626,'#skF_5'),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_626))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_626))
      | ~ m1_pre_topc(C_626,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_627)
      | ~ m1_pre_topc(C_626,A_627)
      | v2_struct_0(C_626)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_486])).

tff(c_315,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_491,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_488,c_315])).

tff(c_494,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46,c_42,c_34,c_28,c_22,c_491])).

tff(c_496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_48,c_494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.57  
% 3.28/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.57  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.28/1.57  
% 3.28/1.57  %Foreground sorts:
% 3.28/1.57  
% 3.28/1.57  
% 3.28/1.57  %Background operators:
% 3.28/1.57  
% 3.28/1.57  
% 3.28/1.57  %Foreground operators:
% 3.28/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.28/1.57  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.28/1.57  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.28/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.57  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.28/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.28/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.28/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.28/1.57  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.28/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.28/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.28/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.28/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.57  
% 3.28/1.60  tff(f_204, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.28/1.60  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.28/1.60  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.28/1.60  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 3.28/1.60  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.28/1.60  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.28/1.60  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_28, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_22, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_20, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_24, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_72, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 3.28/1.60  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_71, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30])).
% 3.28/1.60  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_96, plain, (![B_540, A_541]: (v2_pre_topc(B_540) | ~m1_pre_topc(B_540, A_541) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.60  tff(c_102, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_96])).
% 3.28/1.60  tff(c_111, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_102])).
% 3.28/1.60  tff(c_77, plain, (![B_538, A_539]: (l1_pre_topc(B_538) | ~m1_pre_topc(B_538, A_539) | ~l1_pre_topc(A_539))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.60  tff(c_83, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_77])).
% 3.28/1.60  tff(c_90, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_83])).
% 3.28/1.60  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_26, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_8, plain, (![B_15, D_21, C_19, A_7]: (k1_tops_1(B_15, D_21)=D_21 | ~v3_pre_topc(D_21, B_15) | ~m1_subset_1(D_21, k1_zfmisc_1(u1_struct_0(B_15))) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(B_15) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.28/1.60  tff(c_222, plain, (![C_554, A_555]: (~m1_subset_1(C_554, k1_zfmisc_1(u1_struct_0(A_555))) | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555))), inference(splitLeft, [status(thm)], [c_8])).
% 3.28/1.60  tff(c_225, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_222])).
% 3.28/1.60  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_90, c_225])).
% 3.28/1.60  tff(c_231, plain, (![B_556, D_557]: (k1_tops_1(B_556, D_557)=D_557 | ~v3_pre_topc(D_557, B_556) | ~m1_subset_1(D_557, k1_zfmisc_1(u1_struct_0(B_556))) | ~l1_pre_topc(B_556))), inference(splitRight, [status(thm)], [c_8])).
% 3.28/1.60  tff(c_234, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_231])).
% 3.28/1.60  tff(c_237, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_26, c_234])).
% 3.28/1.60  tff(c_272, plain, (![C_566, A_567, B_568]: (m1_connsp_2(C_566, A_567, B_568) | ~r2_hidden(B_568, k1_tops_1(A_567, C_566)) | ~m1_subset_1(C_566, k1_zfmisc_1(u1_struct_0(A_567))) | ~m1_subset_1(B_568, u1_struct_0(A_567)) | ~l1_pre_topc(A_567) | ~v2_pre_topc(A_567) | v2_struct_0(A_567))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.28/1.60  tff(c_274, plain, (![B_568]: (m1_connsp_2('#skF_6', '#skF_4', B_568) | ~r2_hidden(B_568, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_568, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_272])).
% 3.28/1.60  tff(c_276, plain, (![B_568]: (m1_connsp_2('#skF_6', '#skF_4', B_568) | ~r2_hidden(B_568, '#skF_6') | ~m1_subset_1(B_568, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_90, c_32, c_274])).
% 3.28/1.60  tff(c_278, plain, (![B_569]: (m1_connsp_2('#skF_6', '#skF_4', B_569) | ~r2_hidden(B_569, '#skF_6') | ~m1_subset_1(B_569, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_276])).
% 3.28/1.60  tff(c_281, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_71, c_278])).
% 3.28/1.60  tff(c_284, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_281])).
% 3.28/1.60  tff(c_68, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_69, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_68])).
% 3.28/1.60  tff(c_117, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_69])).
% 3.28/1.60  tff(c_62, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_62])).
% 3.28/1.60  tff(c_158, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_70])).
% 3.28/1.60  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.28/1.60  tff(c_299, plain, (![B_585, E_587, H_582, D_583, A_584, C_586, F_581]: (r1_tmap_1(D_583, B_585, E_587, H_582) | ~r1_tmap_1(C_586, B_585, k3_tmap_1(A_584, B_585, D_583, C_586, E_587), H_582) | ~m1_connsp_2(F_581, D_583, H_582) | ~r1_tarski(F_581, u1_struct_0(C_586)) | ~m1_subset_1(H_582, u1_struct_0(C_586)) | ~m1_subset_1(H_582, u1_struct_0(D_583)) | ~m1_subset_1(F_581, k1_zfmisc_1(u1_struct_0(D_583))) | ~m1_pre_topc(C_586, D_583) | ~m1_subset_1(E_587, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_583), u1_struct_0(B_585)))) | ~v1_funct_2(E_587, u1_struct_0(D_583), u1_struct_0(B_585)) | ~v1_funct_1(E_587) | ~m1_pre_topc(D_583, A_584) | v2_struct_0(D_583) | ~m1_pre_topc(C_586, A_584) | v2_struct_0(C_586) | ~l1_pre_topc(B_585) | ~v2_pre_topc(B_585) | v2_struct_0(B_585) | ~l1_pre_topc(A_584) | ~v2_pre_topc(A_584) | v2_struct_0(A_584))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.28/1.60  tff(c_301, plain, (![F_581]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(F_581, '#skF_4', '#skF_8') | ~r1_tarski(F_581, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_581, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_117, c_299])).
% 3.28/1.60  tff(c_304, plain, (![F_581]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(F_581, '#skF_4', '#skF_8') | ~r1_tarski(F_581, u1_struct_0('#skF_3')) | ~m1_subset_1(F_581, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_46, c_42, c_40, c_38, c_36, c_34, c_71, c_28, c_301])).
% 3.28/1.60  tff(c_306, plain, (![F_588]: (~m1_connsp_2(F_588, '#skF_4', '#skF_8') | ~r1_tarski(F_588, u1_struct_0('#skF_3')) | ~m1_subset_1(F_588, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_48, c_44, c_158, c_304])).
% 3.28/1.60  tff(c_309, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_306])).
% 3.28/1.60  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_284, c_309])).
% 3.28/1.60  tff(c_314, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_69])).
% 3.28/1.60  tff(c_410, plain, (![C_599, A_600]: (~m1_subset_1(C_599, k1_zfmisc_1(u1_struct_0(A_600))) | ~l1_pre_topc(A_600) | ~v2_pre_topc(A_600))), inference(splitLeft, [status(thm)], [c_8])).
% 3.28/1.60  tff(c_413, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_410])).
% 3.28/1.60  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_90, c_413])).
% 3.28/1.60  tff(c_419, plain, (![B_601, D_602]: (k1_tops_1(B_601, D_602)=D_602 | ~v3_pre_topc(D_602, B_601) | ~m1_subset_1(D_602, k1_zfmisc_1(u1_struct_0(B_601))) | ~l1_pre_topc(B_601))), inference(splitRight, [status(thm)], [c_8])).
% 3.28/1.60  tff(c_422, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_419])).
% 3.28/1.60  tff(c_425, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_26, c_422])).
% 3.28/1.60  tff(c_447, plain, (![C_607, A_608, B_609]: (m1_connsp_2(C_607, A_608, B_609) | ~r2_hidden(B_609, k1_tops_1(A_608, C_607)) | ~m1_subset_1(C_607, k1_zfmisc_1(u1_struct_0(A_608))) | ~m1_subset_1(B_609, u1_struct_0(A_608)) | ~l1_pre_topc(A_608) | ~v2_pre_topc(A_608) | v2_struct_0(A_608))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.28/1.60  tff(c_449, plain, (![B_609]: (m1_connsp_2('#skF_6', '#skF_4', B_609) | ~r2_hidden(B_609, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_609, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_447])).
% 3.28/1.60  tff(c_451, plain, (![B_609]: (m1_connsp_2('#skF_6', '#skF_4', B_609) | ~r2_hidden(B_609, '#skF_6') | ~m1_subset_1(B_609, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_90, c_32, c_449])).
% 3.28/1.60  tff(c_453, plain, (![B_610]: (m1_connsp_2('#skF_6', '#skF_4', B_610) | ~r2_hidden(B_610, '#skF_6') | ~m1_subset_1(B_610, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_451])).
% 3.28/1.60  tff(c_456, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_71, c_453])).
% 3.28/1.60  tff(c_459, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_456])).
% 3.28/1.60  tff(c_474, plain, (![B_619, H_616, D_617, F_615, E_621, A_618, C_620]: (r1_tmap_1(C_620, B_619, k3_tmap_1(A_618, B_619, D_617, C_620, E_621), H_616) | ~r1_tmap_1(D_617, B_619, E_621, H_616) | ~m1_connsp_2(F_615, D_617, H_616) | ~r1_tarski(F_615, u1_struct_0(C_620)) | ~m1_subset_1(H_616, u1_struct_0(C_620)) | ~m1_subset_1(H_616, u1_struct_0(D_617)) | ~m1_subset_1(F_615, k1_zfmisc_1(u1_struct_0(D_617))) | ~m1_pre_topc(C_620, D_617) | ~m1_subset_1(E_621, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_617), u1_struct_0(B_619)))) | ~v1_funct_2(E_621, u1_struct_0(D_617), u1_struct_0(B_619)) | ~v1_funct_1(E_621) | ~m1_pre_topc(D_617, A_618) | v2_struct_0(D_617) | ~m1_pre_topc(C_620, A_618) | v2_struct_0(C_620) | ~l1_pre_topc(B_619) | ~v2_pre_topc(B_619) | v2_struct_0(B_619) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.28/1.60  tff(c_476, plain, (![C_620, B_619, A_618, E_621]: (r1_tmap_1(C_620, B_619, k3_tmap_1(A_618, B_619, '#skF_4', C_620, E_621), '#skF_8') | ~r1_tmap_1('#skF_4', B_619, E_621, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_620)) | ~m1_subset_1('#skF_8', u1_struct_0(C_620)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(C_620, '#skF_4') | ~m1_subset_1(E_621, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_619)))) | ~v1_funct_2(E_621, u1_struct_0('#skF_4'), u1_struct_0(B_619)) | ~v1_funct_1(E_621) | ~m1_pre_topc('#skF_4', A_618) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_620, A_618) | v2_struct_0(C_620) | ~l1_pre_topc(B_619) | ~v2_pre_topc(B_619) | v2_struct_0(B_619) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(resolution, [status(thm)], [c_459, c_474])).
% 3.28/1.60  tff(c_479, plain, (![C_620, B_619, A_618, E_621]: (r1_tmap_1(C_620, B_619, k3_tmap_1(A_618, B_619, '#skF_4', C_620, E_621), '#skF_8') | ~r1_tmap_1('#skF_4', B_619, E_621, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_620)) | ~m1_subset_1('#skF_8', u1_struct_0(C_620)) | ~m1_pre_topc(C_620, '#skF_4') | ~m1_subset_1(E_621, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_619)))) | ~v1_funct_2(E_621, u1_struct_0('#skF_4'), u1_struct_0(B_619)) | ~v1_funct_1(E_621) | ~m1_pre_topc('#skF_4', A_618) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_620, A_618) | v2_struct_0(C_620) | ~l1_pre_topc(B_619) | ~v2_pre_topc(B_619) | v2_struct_0(B_619) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_71, c_476])).
% 3.28/1.60  tff(c_481, plain, (![C_622, B_623, A_624, E_625]: (r1_tmap_1(C_622, B_623, k3_tmap_1(A_624, B_623, '#skF_4', C_622, E_625), '#skF_8') | ~r1_tmap_1('#skF_4', B_623, E_625, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_622)) | ~m1_subset_1('#skF_8', u1_struct_0(C_622)) | ~m1_pre_topc(C_622, '#skF_4') | ~m1_subset_1(E_625, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_623)))) | ~v1_funct_2(E_625, u1_struct_0('#skF_4'), u1_struct_0(B_623)) | ~v1_funct_1(E_625) | ~m1_pre_topc('#skF_4', A_624) | ~m1_pre_topc(C_622, A_624) | v2_struct_0(C_622) | ~l1_pre_topc(B_623) | ~v2_pre_topc(B_623) | v2_struct_0(B_623) | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(negUnitSimplification, [status(thm)], [c_44, c_479])).
% 3.28/1.60  tff(c_483, plain, (![C_622, A_624]: (r1_tmap_1(C_622, '#skF_2', k3_tmap_1(A_624, '#skF_2', '#skF_4', C_622, '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_622)) | ~m1_subset_1('#skF_8', u1_struct_0(C_622)) | ~m1_pre_topc(C_622, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_624) | ~m1_pre_topc(C_622, A_624) | v2_struct_0(C_622) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(resolution, [status(thm)], [c_36, c_481])).
% 3.28/1.60  tff(c_486, plain, (![C_622, A_624]: (r1_tmap_1(C_622, '#skF_2', k3_tmap_1(A_624, '#skF_2', '#skF_4', C_622, '#skF_5'), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_622)) | ~m1_subset_1('#skF_8', u1_struct_0(C_622)) | ~m1_pre_topc(C_622, '#skF_4') | ~m1_pre_topc('#skF_4', A_624) | ~m1_pre_topc(C_622, A_624) | v2_struct_0(C_622) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_314, c_483])).
% 3.28/1.60  tff(c_488, plain, (![C_626, A_627]: (r1_tmap_1(C_626, '#skF_2', k3_tmap_1(A_627, '#skF_2', '#skF_4', C_626, '#skF_5'), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_626)) | ~m1_subset_1('#skF_8', u1_struct_0(C_626)) | ~m1_pre_topc(C_626, '#skF_4') | ~m1_pre_topc('#skF_4', A_627) | ~m1_pre_topc(C_626, A_627) | v2_struct_0(C_626) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(negUnitSimplification, [status(thm)], [c_54, c_486])).
% 3.28/1.60  tff(c_315, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_69])).
% 3.28/1.60  tff(c_491, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_488, c_315])).
% 3.28/1.60  tff(c_494, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46, c_42, c_34, c_28, c_22, c_491])).
% 3.28/1.60  tff(c_496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_48, c_494])).
% 3.28/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.60  
% 3.28/1.60  Inference rules
% 3.28/1.60  ----------------------
% 3.28/1.60  #Ref     : 0
% 3.28/1.60  #Sup     : 74
% 3.28/1.60  #Fact    : 0
% 3.28/1.60  #Define  : 0
% 3.28/1.60  #Split   : 6
% 3.28/1.60  #Chain   : 0
% 3.28/1.60  #Close   : 0
% 3.28/1.60  
% 3.28/1.60  Ordering : KBO
% 3.28/1.60  
% 3.28/1.60  Simplification rules
% 3.28/1.60  ----------------------
% 3.28/1.60  #Subsume      : 12
% 3.28/1.60  #Demod        : 171
% 3.28/1.60  #Tautology    : 34
% 3.28/1.60  #SimpNegUnit  : 10
% 3.28/1.60  #BackRed      : 0
% 3.28/1.60  
% 3.28/1.60  #Partial instantiations: 0
% 3.28/1.60  #Strategies tried      : 1
% 3.28/1.60  
% 3.28/1.60  Timing (in seconds)
% 3.28/1.60  ----------------------
% 3.28/1.60  Preprocessing        : 0.40
% 3.28/1.60  Parsing              : 0.19
% 3.28/1.60  CNF conversion       : 0.07
% 3.28/1.60  Main loop            : 0.34
% 3.28/1.60  Inferencing          : 0.12
% 3.28/1.60  Reduction            : 0.11
% 3.28/1.60  Demodulation         : 0.08
% 3.28/1.60  BG Simplification    : 0.02
% 3.28/1.60  Subsumption          : 0.06
% 3.28/1.60  Abstraction          : 0.01
% 3.28/1.60  MUC search           : 0.00
% 3.28/1.60  Cooper               : 0.00
% 3.28/1.60  Total                : 0.79
% 3.28/1.60  Index Insertion      : 0.00
% 3.28/1.60  Index Deletion       : 0.00
% 3.28/1.60  Index Matching       : 0.00
% 3.28/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
