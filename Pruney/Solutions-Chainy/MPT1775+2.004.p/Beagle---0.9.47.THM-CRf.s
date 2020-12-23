%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:27 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 423 expanded)
%              Number of leaves         :   42 ( 175 expanded)
%              Depth                    :   16
%              Number of atoms          :  384 (3003 expanded)
%              Number of equality atoms :    6 ( 129 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_281,negated_conjecture,(
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
                       => ( ( v1_tsep_1(C,D)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,B,E,F)
                                    <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_230,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_175,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_38,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_83,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_91,plain,(
    ! [B_544,A_545] :
      ( l1_pre_topc(B_544)
      | ~ m1_pre_topc(B_544,A_545)
      | ~ l1_pre_topc(A_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_91])).

tff(c_106,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_97])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_91])).

tff(c_103,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_94])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    ! [B_557,A_558] :
      ( m1_subset_1(u1_struct_0(B_557),k1_zfmisc_1(u1_struct_0(A_558)))
      | ~ m1_pre_topc(B_557,A_558)
      | ~ l1_pre_topc(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_189,plain,(
    ! [A_565,A_566,B_567] :
      ( m1_subset_1(A_565,u1_struct_0(A_566))
      | ~ r2_hidden(A_565,u1_struct_0(B_567))
      | ~ m1_pre_topc(B_567,A_566)
      | ~ l1_pre_topc(A_566) ) ),
    inference(resolution,[status(thm)],[c_146,c_10])).

tff(c_196,plain,(
    ! [A_568,A_569,B_570] :
      ( m1_subset_1(A_568,u1_struct_0(A_569))
      | ~ m1_pre_topc(B_570,A_569)
      | ~ l1_pre_topc(A_569)
      | v1_xboole_0(u1_struct_0(B_570))
      | ~ m1_subset_1(A_568,u1_struct_0(B_570)) ) ),
    inference(resolution,[status(thm)],[c_8,c_189])).

tff(c_206,plain,(
    ! [A_568] :
      ( m1_subset_1(A_568,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_568,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_196])).

tff(c_217,plain,(
    ! [A_568] :
      ( m1_subset_1(A_568,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_568,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_206])).

tff(c_240,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_18,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_243,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_18])).

tff(c_246,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_243])).

tff(c_249,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_246])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_249])).

tff(c_255,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_119,plain,(
    ! [B_551,A_552] :
      ( v2_pre_topc(B_551)
      | ~ m1_pre_topc(B_551,A_552)
      | ~ l1_pre_topc(A_552)
      | ~ v2_pre_topc(A_552) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_119])).

tff(c_131,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_122])).

tff(c_46,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_28,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(u1_struct_0(B_32),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_390,plain,(
    ! [B_590,A_591] :
      ( v3_pre_topc(u1_struct_0(B_590),A_591)
      | ~ v1_tsep_1(B_590,A_591)
      | ~ m1_subset_1(u1_struct_0(B_590),k1_zfmisc_1(u1_struct_0(A_591)))
      | ~ m1_pre_topc(B_590,A_591)
      | ~ l1_pre_topc(A_591)
      | ~ v2_pre_topc(A_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_394,plain,(
    ! [B_32,A_30] :
      ( v3_pre_topc(u1_struct_0(B_32),A_30)
      | ~ v1_tsep_1(B_32,A_30)
      | ~ v2_pre_topc(A_30)
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_28,c_390])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_400,plain,(
    ! [B_594,A_595,C_596] :
      ( m1_connsp_2(B_594,A_595,C_596)
      | ~ r2_hidden(C_596,B_594)
      | ~ v3_pre_topc(B_594,A_595)
      | ~ m1_subset_1(C_596,u1_struct_0(A_595))
      | ~ m1_subset_1(B_594,k1_zfmisc_1(u1_struct_0(A_595)))
      | ~ l1_pre_topc(A_595)
      | ~ v2_pre_topc(A_595)
      | v2_struct_0(A_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_410,plain,(
    ! [B_594] :
      ( m1_connsp_2(B_594,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_594)
      | ~ v3_pre_topc(B_594,'#skF_4')
      | ~ m1_subset_1(B_594,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_400])).

tff(c_425,plain,(
    ! [B_594] :
      ( m1_connsp_2(B_594,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_594)
      | ~ v3_pre_topc(B_594,'#skF_4')
      | ~ m1_subset_1(B_594,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_103,c_410])).

tff(c_431,plain,(
    ! [B_597] :
      ( m1_connsp_2(B_597,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_597)
      | ~ v3_pre_topc(B_597,'#skF_4')
      | ~ m1_subset_1(B_597,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_425])).

tff(c_435,plain,(
    ! [B_32] :
      ( m1_connsp_2(u1_struct_0(B_32),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_32))
      | ~ v3_pre_topc(u1_struct_0(B_32),'#skF_4')
      | ~ m1_pre_topc(B_32,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_431])).

tff(c_438,plain,(
    ! [B_32] :
      ( m1_connsp_2(u1_struct_0(B_32),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_32))
      | ~ v3_pre_topc(u1_struct_0(B_32),'#skF_4')
      | ~ m1_pre_topc(B_32,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_435])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_81,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_138,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_74])).

tff(c_195,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_82])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_486,plain,(
    ! [F_628,D_626,C_624,H_625,A_627,E_630,B_629] :
      ( r1_tmap_1(D_626,B_629,E_630,H_625)
      | ~ r1_tmap_1(C_624,B_629,k3_tmap_1(A_627,B_629,D_626,C_624,E_630),H_625)
      | ~ m1_connsp_2(F_628,D_626,H_625)
      | ~ r1_tarski(F_628,u1_struct_0(C_624))
      | ~ m1_subset_1(H_625,u1_struct_0(C_624))
      | ~ m1_subset_1(H_625,u1_struct_0(D_626))
      | ~ m1_subset_1(F_628,k1_zfmisc_1(u1_struct_0(D_626)))
      | ~ m1_pre_topc(C_624,D_626)
      | ~ m1_subset_1(E_630,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_626),u1_struct_0(B_629))))
      | ~ v1_funct_2(E_630,u1_struct_0(D_626),u1_struct_0(B_629))
      | ~ v1_funct_1(E_630)
      | ~ m1_pre_topc(D_626,A_627)
      | v2_struct_0(D_626)
      | ~ m1_pre_topc(C_624,A_627)
      | v2_struct_0(C_624)
      | ~ l1_pre_topc(B_629)
      | ~ v2_pre_topc(B_629)
      | v2_struct_0(B_629)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_490,plain,(
    ! [F_628] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_628,'#skF_4','#skF_6')
      | ~ r1_tarski(F_628,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_628,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_138,c_486])).

tff(c_497,plain,(
    ! [F_628] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_628,'#skF_4','#skF_6')
      | ~ r1_tarski(F_628,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_628,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_50,c_48,c_44,c_42,c_83,c_490])).

tff(c_499,plain,(
    ! [F_631] :
      ( ~ m1_connsp_2(F_631,'#skF_4','#skF_6')
      | ~ r1_tarski(F_631,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_631,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_195,c_497])).

tff(c_503,plain,(
    ! [B_32] :
      ( ~ m1_connsp_2(u1_struct_0(B_32),'#skF_4','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_32),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_32,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_499])).

tff(c_507,plain,(
    ! [B_632] :
      ( ~ m1_connsp_2(u1_struct_0(B_632),'#skF_4','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_632),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_632,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_503])).

tff(c_511,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_3'),'#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_507])).

tff(c_514,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_3'),'#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_511])).

tff(c_523,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_438,c_514])).

tff(c_534,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_523])).

tff(c_535,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_534])).

tff(c_538,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_394,c_535])).

tff(c_542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_131,c_46,c_538])).

tff(c_543,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_556,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_543])).

tff(c_559,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_556])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_559])).

tff(c_562,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_881,plain,(
    ! [A_680,E_681,G_683,D_684,C_685,B_682] :
      ( r1_tmap_1(D_684,B_682,k3_tmap_1(A_680,B_682,C_685,D_684,E_681),G_683)
      | ~ r1_tmap_1(C_685,B_682,E_681,G_683)
      | ~ m1_pre_topc(D_684,C_685)
      | ~ m1_subset_1(G_683,u1_struct_0(D_684))
      | ~ m1_subset_1(G_683,u1_struct_0(C_685))
      | ~ m1_subset_1(E_681,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_685),u1_struct_0(B_682))))
      | ~ v1_funct_2(E_681,u1_struct_0(C_685),u1_struct_0(B_682))
      | ~ v1_funct_1(E_681)
      | ~ m1_pre_topc(D_684,A_680)
      | v2_struct_0(D_684)
      | ~ m1_pre_topc(C_685,A_680)
      | v2_struct_0(C_685)
      | ~ l1_pre_topc(B_682)
      | ~ v2_pre_topc(B_682)
      | v2_struct_0(B_682)
      | ~ l1_pre_topc(A_680)
      | ~ v2_pre_topc(A_680)
      | v2_struct_0(A_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_883,plain,(
    ! [D_684,A_680,G_683] :
      ( r1_tmap_1(D_684,'#skF_2',k3_tmap_1(A_680,'#skF_2','#skF_4',D_684,'#skF_5'),G_683)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_683)
      | ~ m1_pre_topc(D_684,'#skF_4')
      | ~ m1_subset_1(G_683,u1_struct_0(D_684))
      | ~ m1_subset_1(G_683,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_684,A_680)
      | v2_struct_0(D_684)
      | ~ m1_pre_topc('#skF_4',A_680)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_680)
      | ~ v2_pre_topc(A_680)
      | v2_struct_0(A_680) ) ),
    inference(resolution,[status(thm)],[c_48,c_881])).

tff(c_886,plain,(
    ! [D_684,A_680,G_683] :
      ( r1_tmap_1(D_684,'#skF_2',k3_tmap_1(A_680,'#skF_2','#skF_4',D_684,'#skF_5'),G_683)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_683)
      | ~ m1_pre_topc(D_684,'#skF_4')
      | ~ m1_subset_1(G_683,u1_struct_0(D_684))
      | ~ m1_subset_1(G_683,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_684,A_680)
      | v2_struct_0(D_684)
      | ~ m1_pre_topc('#skF_4',A_680)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_680)
      | ~ v2_pre_topc(A_680)
      | v2_struct_0(A_680) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_50,c_883])).

tff(c_912,plain,(
    ! [D_708,A_709,G_710] :
      ( r1_tmap_1(D_708,'#skF_2',k3_tmap_1(A_709,'#skF_2','#skF_4',D_708,'#skF_5'),G_710)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_710)
      | ~ m1_pre_topc(D_708,'#skF_4')
      | ~ m1_subset_1(G_710,u1_struct_0(D_708))
      | ~ m1_subset_1(G_710,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_708,A_709)
      | v2_struct_0(D_708)
      | ~ m1_pre_topc('#skF_4',A_709)
      | ~ l1_pre_topc(A_709)
      | ~ v2_pre_topc(A_709)
      | v2_struct_0(A_709) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_56,c_886])).

tff(c_563,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_917,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_912,c_563])).

tff(c_924,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_42,c_83,c_44,c_562,c_917])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60,c_924])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.74  
% 4.17/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.74  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.17/1.74  
% 4.17/1.74  %Foreground sorts:
% 4.17/1.74  
% 4.17/1.74  
% 4.17/1.74  %Background operators:
% 4.17/1.74  
% 4.17/1.74  
% 4.17/1.74  %Foreground operators:
% 4.17/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.17/1.74  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.17/1.74  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.17/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.17/1.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.17/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.17/1.74  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.17/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.17/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.17/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.17/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.17/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.17/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.17/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.17/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.17/1.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.17/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.17/1.74  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.17/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.17/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.74  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.17/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.17/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.17/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.17/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.17/1.74  
% 4.17/1.77  tff(f_281, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.17/1.77  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.17/1.77  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.17/1.77  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.17/1.77  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.17/1.77  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.17/1.77  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.17/1.77  tff(f_52, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.17/1.77  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.17/1.77  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.17/1.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.17/1.77  tff(f_230, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.17/1.77  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.17/1.77  tff(c_72, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_38, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_40, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_83, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 4.17/1.77  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_91, plain, (![B_544, A_545]: (l1_pre_topc(B_544) | ~m1_pre_topc(B_544, A_545) | ~l1_pre_topc(A_545))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.17/1.77  tff(c_97, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_91])).
% 4.17/1.77  tff(c_106, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_97])).
% 4.17/1.77  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.77  tff(c_94, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_91])).
% 4.17/1.77  tff(c_103, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_94])).
% 4.17/1.77  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.17/1.77  tff(c_146, plain, (![B_557, A_558]: (m1_subset_1(u1_struct_0(B_557), k1_zfmisc_1(u1_struct_0(A_558))) | ~m1_pre_topc(B_557, A_558) | ~l1_pre_topc(A_558))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.17/1.77  tff(c_10, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.17/1.77  tff(c_189, plain, (![A_565, A_566, B_567]: (m1_subset_1(A_565, u1_struct_0(A_566)) | ~r2_hidden(A_565, u1_struct_0(B_567)) | ~m1_pre_topc(B_567, A_566) | ~l1_pre_topc(A_566))), inference(resolution, [status(thm)], [c_146, c_10])).
% 4.17/1.77  tff(c_196, plain, (![A_568, A_569, B_570]: (m1_subset_1(A_568, u1_struct_0(A_569)) | ~m1_pre_topc(B_570, A_569) | ~l1_pre_topc(A_569) | v1_xboole_0(u1_struct_0(B_570)) | ~m1_subset_1(A_568, u1_struct_0(B_570)))), inference(resolution, [status(thm)], [c_8, c_189])).
% 4.17/1.77  tff(c_206, plain, (![A_568]: (m1_subset_1(A_568, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_568, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_196])).
% 4.17/1.77  tff(c_217, plain, (![A_568]: (m1_subset_1(A_568, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_568, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_206])).
% 4.17/1.77  tff(c_240, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_217])).
% 4.17/1.77  tff(c_18, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.17/1.77  tff(c_243, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_240, c_18])).
% 4.17/1.77  tff(c_246, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_243])).
% 4.17/1.77  tff(c_249, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_246])).
% 4.17/1.77  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_249])).
% 4.17/1.77  tff(c_255, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_217])).
% 4.17/1.77  tff(c_119, plain, (![B_551, A_552]: (v2_pre_topc(B_551) | ~m1_pre_topc(B_551, A_552) | ~l1_pre_topc(A_552) | ~v2_pre_topc(A_552))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.17/1.77  tff(c_122, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_119])).
% 4.17/1.77  tff(c_131, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_122])).
% 4.17/1.77  tff(c_46, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_28, plain, (![B_32, A_30]: (m1_subset_1(u1_struct_0(B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.17/1.77  tff(c_390, plain, (![B_590, A_591]: (v3_pre_topc(u1_struct_0(B_590), A_591) | ~v1_tsep_1(B_590, A_591) | ~m1_subset_1(u1_struct_0(B_590), k1_zfmisc_1(u1_struct_0(A_591))) | ~m1_pre_topc(B_590, A_591) | ~l1_pre_topc(A_591) | ~v2_pre_topc(A_591))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.17/1.77  tff(c_394, plain, (![B_32, A_30]: (v3_pre_topc(u1_struct_0(B_32), A_30) | ~v1_tsep_1(B_32, A_30) | ~v2_pre_topc(A_30) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_28, c_390])).
% 4.17/1.77  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_400, plain, (![B_594, A_595, C_596]: (m1_connsp_2(B_594, A_595, C_596) | ~r2_hidden(C_596, B_594) | ~v3_pre_topc(B_594, A_595) | ~m1_subset_1(C_596, u1_struct_0(A_595)) | ~m1_subset_1(B_594, k1_zfmisc_1(u1_struct_0(A_595))) | ~l1_pre_topc(A_595) | ~v2_pre_topc(A_595) | v2_struct_0(A_595))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.17/1.77  tff(c_410, plain, (![B_594]: (m1_connsp_2(B_594, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_594) | ~v3_pre_topc(B_594, '#skF_4') | ~m1_subset_1(B_594, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_400])).
% 4.17/1.77  tff(c_425, plain, (![B_594]: (m1_connsp_2(B_594, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_594) | ~v3_pre_topc(B_594, '#skF_4') | ~m1_subset_1(B_594, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_103, c_410])).
% 4.17/1.77  tff(c_431, plain, (![B_597]: (m1_connsp_2(B_597, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_597) | ~v3_pre_topc(B_597, '#skF_4') | ~m1_subset_1(B_597, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_425])).
% 4.17/1.77  tff(c_435, plain, (![B_32]: (m1_connsp_2(u1_struct_0(B_32), '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_32)) | ~v3_pre_topc(u1_struct_0(B_32), '#skF_4') | ~m1_pre_topc(B_32, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_431])).
% 4.17/1.77  tff(c_438, plain, (![B_32]: (m1_connsp_2(u1_struct_0(B_32), '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_32)) | ~v3_pre_topc(u1_struct_0(B_32), '#skF_4') | ~m1_pre_topc(B_32, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_435])).
% 4.17/1.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.17/1.77  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_80, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_81, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_80])).
% 4.17/1.77  tff(c_138, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_81])).
% 4.17/1.77  tff(c_74, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_82, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_74])).
% 4.17/1.77  tff(c_195, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_82])).
% 4.17/1.77  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_50, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_281])).
% 4.17/1.77  tff(c_486, plain, (![F_628, D_626, C_624, H_625, A_627, E_630, B_629]: (r1_tmap_1(D_626, B_629, E_630, H_625) | ~r1_tmap_1(C_624, B_629, k3_tmap_1(A_627, B_629, D_626, C_624, E_630), H_625) | ~m1_connsp_2(F_628, D_626, H_625) | ~r1_tarski(F_628, u1_struct_0(C_624)) | ~m1_subset_1(H_625, u1_struct_0(C_624)) | ~m1_subset_1(H_625, u1_struct_0(D_626)) | ~m1_subset_1(F_628, k1_zfmisc_1(u1_struct_0(D_626))) | ~m1_pre_topc(C_624, D_626) | ~m1_subset_1(E_630, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_626), u1_struct_0(B_629)))) | ~v1_funct_2(E_630, u1_struct_0(D_626), u1_struct_0(B_629)) | ~v1_funct_1(E_630) | ~m1_pre_topc(D_626, A_627) | v2_struct_0(D_626) | ~m1_pre_topc(C_624, A_627) | v2_struct_0(C_624) | ~l1_pre_topc(B_629) | ~v2_pre_topc(B_629) | v2_struct_0(B_629) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(cnfTransformation, [status(thm)], [f_230])).
% 4.17/1.77  tff(c_490, plain, (![F_628]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_628, '#skF_4', '#skF_6') | ~r1_tarski(F_628, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_628, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_138, c_486])).
% 4.17/1.77  tff(c_497, plain, (![F_628]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_628, '#skF_4', '#skF_6') | ~r1_tarski(F_628, u1_struct_0('#skF_3')) | ~m1_subset_1(F_628, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_50, c_48, c_44, c_42, c_83, c_490])).
% 4.17/1.77  tff(c_499, plain, (![F_631]: (~m1_connsp_2(F_631, '#skF_4', '#skF_6') | ~r1_tarski(F_631, u1_struct_0('#skF_3')) | ~m1_subset_1(F_631, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_195, c_497])).
% 4.17/1.77  tff(c_503, plain, (![B_32]: (~m1_connsp_2(u1_struct_0(B_32), '#skF_4', '#skF_6') | ~r1_tarski(u1_struct_0(B_32), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_32, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_499])).
% 4.17/1.77  tff(c_507, plain, (![B_632]: (~m1_connsp_2(u1_struct_0(B_632), '#skF_4', '#skF_6') | ~r1_tarski(u1_struct_0(B_632), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_632, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_503])).
% 4.17/1.77  tff(c_511, plain, (~m1_connsp_2(u1_struct_0('#skF_3'), '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6, c_507])).
% 4.17/1.77  tff(c_514, plain, (~m1_connsp_2(u1_struct_0('#skF_3'), '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_511])).
% 4.17/1.77  tff(c_523, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_438, c_514])).
% 4.17/1.77  tff(c_534, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_523])).
% 4.17/1.77  tff(c_535, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_534])).
% 4.17/1.77  tff(c_538, plain, (~v1_tsep_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_394, c_535])).
% 4.17/1.77  tff(c_542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_131, c_46, c_538])).
% 4.17/1.77  tff(c_543, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_534])).
% 4.17/1.77  tff(c_556, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_543])).
% 4.17/1.77  tff(c_559, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_556])).
% 4.17/1.77  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_559])).
% 4.17/1.77  tff(c_562, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_81])).
% 4.17/1.77  tff(c_881, plain, (![A_680, E_681, G_683, D_684, C_685, B_682]: (r1_tmap_1(D_684, B_682, k3_tmap_1(A_680, B_682, C_685, D_684, E_681), G_683) | ~r1_tmap_1(C_685, B_682, E_681, G_683) | ~m1_pre_topc(D_684, C_685) | ~m1_subset_1(G_683, u1_struct_0(D_684)) | ~m1_subset_1(G_683, u1_struct_0(C_685)) | ~m1_subset_1(E_681, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_685), u1_struct_0(B_682)))) | ~v1_funct_2(E_681, u1_struct_0(C_685), u1_struct_0(B_682)) | ~v1_funct_1(E_681) | ~m1_pre_topc(D_684, A_680) | v2_struct_0(D_684) | ~m1_pre_topc(C_685, A_680) | v2_struct_0(C_685) | ~l1_pre_topc(B_682) | ~v2_pre_topc(B_682) | v2_struct_0(B_682) | ~l1_pre_topc(A_680) | ~v2_pre_topc(A_680) | v2_struct_0(A_680))), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.17/1.77  tff(c_883, plain, (![D_684, A_680, G_683]: (r1_tmap_1(D_684, '#skF_2', k3_tmap_1(A_680, '#skF_2', '#skF_4', D_684, '#skF_5'), G_683) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_683) | ~m1_pre_topc(D_684, '#skF_4') | ~m1_subset_1(G_683, u1_struct_0(D_684)) | ~m1_subset_1(G_683, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_684, A_680) | v2_struct_0(D_684) | ~m1_pre_topc('#skF_4', A_680) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_680) | ~v2_pre_topc(A_680) | v2_struct_0(A_680))), inference(resolution, [status(thm)], [c_48, c_881])).
% 4.17/1.77  tff(c_886, plain, (![D_684, A_680, G_683]: (r1_tmap_1(D_684, '#skF_2', k3_tmap_1(A_680, '#skF_2', '#skF_4', D_684, '#skF_5'), G_683) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_683) | ~m1_pre_topc(D_684, '#skF_4') | ~m1_subset_1(G_683, u1_struct_0(D_684)) | ~m1_subset_1(G_683, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_684, A_680) | v2_struct_0(D_684) | ~m1_pre_topc('#skF_4', A_680) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_680) | ~v2_pre_topc(A_680) | v2_struct_0(A_680))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_50, c_883])).
% 4.17/1.77  tff(c_912, plain, (![D_708, A_709, G_710]: (r1_tmap_1(D_708, '#skF_2', k3_tmap_1(A_709, '#skF_2', '#skF_4', D_708, '#skF_5'), G_710) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_710) | ~m1_pre_topc(D_708, '#skF_4') | ~m1_subset_1(G_710, u1_struct_0(D_708)) | ~m1_subset_1(G_710, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_708, A_709) | v2_struct_0(D_708) | ~m1_pre_topc('#skF_4', A_709) | ~l1_pre_topc(A_709) | ~v2_pre_topc(A_709) | v2_struct_0(A_709))), inference(negUnitSimplification, [status(thm)], [c_66, c_56, c_886])).
% 4.17/1.77  tff(c_563, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_81])).
% 4.17/1.77  tff(c_917, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_912, c_563])).
% 4.17/1.77  tff(c_924, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_42, c_83, c_44, c_562, c_917])).
% 4.17/1.77  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_60, c_924])).
% 4.17/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.77  
% 4.17/1.77  Inference rules
% 4.17/1.77  ----------------------
% 4.17/1.77  #Ref     : 0
% 4.17/1.77  #Sup     : 141
% 4.17/1.77  #Fact    : 0
% 4.17/1.77  #Define  : 0
% 4.17/1.77  #Split   : 8
% 4.17/1.77  #Chain   : 0
% 4.17/1.77  #Close   : 0
% 4.17/1.77  
% 4.17/1.77  Ordering : KBO
% 4.17/1.77  
% 4.17/1.77  Simplification rules
% 4.17/1.77  ----------------------
% 4.17/1.77  #Subsume      : 22
% 4.17/1.77  #Demod        : 237
% 4.17/1.77  #Tautology    : 45
% 4.17/1.77  #SimpNegUnit  : 27
% 4.17/1.77  #BackRed      : 0
% 4.17/1.77  
% 4.17/1.77  #Partial instantiations: 0
% 4.17/1.77  #Strategies tried      : 1
% 4.17/1.77  
% 4.17/1.77  Timing (in seconds)
% 4.17/1.77  ----------------------
% 4.17/1.78  Preprocessing        : 0.44
% 4.17/1.78  Parsing              : 0.21
% 4.17/1.78  CNF conversion       : 0.07
% 4.17/1.78  Main loop            : 0.54
% 4.17/1.78  Inferencing          : 0.21
% 4.17/1.78  Reduction            : 0.17
% 4.17/1.78  Demodulation         : 0.12
% 4.17/1.78  BG Simplification    : 0.03
% 4.17/1.78  Subsumption          : 0.10
% 4.17/1.78  Abstraction          : 0.02
% 4.17/1.78  MUC search           : 0.00
% 4.17/1.78  Cooper               : 0.00
% 4.17/1.78  Total                : 1.04
% 4.17/1.78  Index Insertion      : 0.00
% 4.17/1.78  Index Deletion       : 0.00
% 4.17/1.78  Index Matching       : 0.00
% 4.17/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
