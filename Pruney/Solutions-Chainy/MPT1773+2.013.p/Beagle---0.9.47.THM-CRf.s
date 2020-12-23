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
% DateTime   : Thu Dec  3 10:27:23 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 235 expanded)
%              Number of leaves         :   32 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :  345 (2092 expanded)
%              Number of equality atoms :    3 (  85 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_185,negated_conjecture,(
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

tff(f_60,axiom,(
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

tff(f_127,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_22,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_16,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_20,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_14,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_18,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_66,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_90,plain,(
    ! [B_525,A_526] :
      ( v2_pre_topc(B_525)
      | ~ m1_pre_topc(B_525,A_526)
      | ~ l1_pre_topc(A_526)
      | ~ v2_pre_topc(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_108,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_99])).

tff(c_71,plain,(
    ! [B_523,A_524] :
      ( l1_pre_topc(B_523)
      | ~ m1_pre_topc(B_523,A_524)
      | ~ l1_pre_topc(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_87,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_80])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_65,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_205,plain,(
    ! [B_537,A_538,C_539] :
      ( m1_connsp_2(B_537,A_538,C_539)
      | ~ r2_hidden(C_539,B_537)
      | ~ v3_pre_topc(B_537,A_538)
      | ~ m1_subset_1(C_539,u1_struct_0(A_538))
      | ~ m1_subset_1(B_537,k1_zfmisc_1(u1_struct_0(A_538)))
      | ~ l1_pre_topc(A_538)
      | ~ v2_pre_topc(A_538)
      | v2_struct_0(A_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_207,plain,(
    ! [B_537] :
      ( m1_connsp_2(B_537,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_537)
      | ~ v3_pre_topc(B_537,'#skF_4')
      | ~ m1_subset_1(B_537,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_205])).

tff(c_212,plain,(
    ! [B_537] :
      ( m1_connsp_2(B_537,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_537)
      | ~ v3_pre_topc(B_537,'#skF_4')
      | ~ m1_subset_1(B_537,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_87,c_207])).

tff(c_218,plain,(
    ! [B_540] :
      ( m1_connsp_2(B_540,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_540)
      | ~ v3_pre_topc(B_540,'#skF_4')
      | ~ m1_subset_1(B_540,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_212])).

tff(c_221,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_218])).

tff(c_224,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66,c_221])).

tff(c_62,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_63,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_111,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_56,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_56])).

tff(c_152,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_64])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_240,plain,(
    ! [D_555,F_553,H_558,B_559,E_556,C_557,A_554] :
      ( r1_tmap_1(D_555,B_559,E_556,H_558)
      | ~ r1_tmap_1(C_557,B_559,k3_tmap_1(A_554,B_559,D_555,C_557,E_556),H_558)
      | ~ m1_connsp_2(F_553,D_555,H_558)
      | ~ r1_tarski(F_553,u1_struct_0(C_557))
      | ~ m1_subset_1(H_558,u1_struct_0(C_557))
      | ~ m1_subset_1(H_558,u1_struct_0(D_555))
      | ~ m1_subset_1(F_553,k1_zfmisc_1(u1_struct_0(D_555)))
      | ~ m1_pre_topc(C_557,D_555)
      | ~ m1_subset_1(E_556,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_555),u1_struct_0(B_559))))
      | ~ v1_funct_2(E_556,u1_struct_0(D_555),u1_struct_0(B_559))
      | ~ v1_funct_1(E_556)
      | ~ m1_pre_topc(D_555,A_554)
      | v2_struct_0(D_555)
      | ~ m1_pre_topc(C_557,A_554)
      | v2_struct_0(C_557)
      | ~ l1_pre_topc(B_559)
      | ~ v2_pre_topc(B_559)
      | v2_struct_0(B_559)
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554)
      | v2_struct_0(A_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_242,plain,(
    ! [F_553] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_553,'#skF_4','#skF_8')
      | ~ r1_tarski(F_553,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_553,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_111,c_240])).

tff(c_245,plain,(
    ! [F_553] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_553,'#skF_4','#skF_8')
      | ~ r1_tarski(F_553,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_553,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_40,c_36,c_34,c_32,c_30,c_28,c_65,c_22,c_242])).

tff(c_247,plain,(
    ! [F_560] :
      ( ~ m1_connsp_2(F_560,'#skF_4','#skF_8')
      | ~ r1_tarski(F_560,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_560,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_42,c_38,c_152,c_245])).

tff(c_250,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_247])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_224,c_250])).

tff(c_255,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_350,plain,(
    ! [B_571,A_572,C_573] :
      ( m1_connsp_2(B_571,A_572,C_573)
      | ~ r2_hidden(C_573,B_571)
      | ~ v3_pre_topc(B_571,A_572)
      | ~ m1_subset_1(C_573,u1_struct_0(A_572))
      | ~ m1_subset_1(B_571,k1_zfmisc_1(u1_struct_0(A_572)))
      | ~ l1_pre_topc(A_572)
      | ~ v2_pre_topc(A_572)
      | v2_struct_0(A_572) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_352,plain,(
    ! [B_571] :
      ( m1_connsp_2(B_571,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_571)
      | ~ v3_pre_topc(B_571,'#skF_4')
      | ~ m1_subset_1(B_571,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_350])).

tff(c_357,plain,(
    ! [B_571] :
      ( m1_connsp_2(B_571,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_571)
      | ~ v3_pre_topc(B_571,'#skF_4')
      | ~ m1_subset_1(B_571,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_87,c_352])).

tff(c_363,plain,(
    ! [B_574] :
      ( m1_connsp_2(B_574,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_574)
      | ~ v3_pre_topc(B_574,'#skF_4')
      | ~ m1_subset_1(B_574,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_357])).

tff(c_366,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_363])).

tff(c_369,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66,c_366])).

tff(c_371,plain,(
    ! [F_576,D_578,A_577,C_580,B_582,E_579,H_581] :
      ( r1_tmap_1(C_580,B_582,k3_tmap_1(A_577,B_582,D_578,C_580,E_579),H_581)
      | ~ r1_tmap_1(D_578,B_582,E_579,H_581)
      | ~ m1_connsp_2(F_576,D_578,H_581)
      | ~ r1_tarski(F_576,u1_struct_0(C_580))
      | ~ m1_subset_1(H_581,u1_struct_0(C_580))
      | ~ m1_subset_1(H_581,u1_struct_0(D_578))
      | ~ m1_subset_1(F_576,k1_zfmisc_1(u1_struct_0(D_578)))
      | ~ m1_pre_topc(C_580,D_578)
      | ~ m1_subset_1(E_579,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_578),u1_struct_0(B_582))))
      | ~ v1_funct_2(E_579,u1_struct_0(D_578),u1_struct_0(B_582))
      | ~ v1_funct_1(E_579)
      | ~ m1_pre_topc(D_578,A_577)
      | v2_struct_0(D_578)
      | ~ m1_pre_topc(C_580,A_577)
      | v2_struct_0(C_580)
      | ~ l1_pre_topc(B_582)
      | ~ v2_pre_topc(B_582)
      | v2_struct_0(B_582)
      | ~ l1_pre_topc(A_577)
      | ~ v2_pre_topc(A_577)
      | v2_struct_0(A_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_373,plain,(
    ! [C_580,B_582,A_577,E_579] :
      ( r1_tmap_1(C_580,B_582,k3_tmap_1(A_577,B_582,'#skF_4',C_580,E_579),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_582,E_579,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_580))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_580))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(C_580,'#skF_4')
      | ~ m1_subset_1(E_579,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_582))))
      | ~ v1_funct_2(E_579,u1_struct_0('#skF_4'),u1_struct_0(B_582))
      | ~ v1_funct_1(E_579)
      | ~ m1_pre_topc('#skF_4',A_577)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_580,A_577)
      | v2_struct_0(C_580)
      | ~ l1_pre_topc(B_582)
      | ~ v2_pre_topc(B_582)
      | v2_struct_0(B_582)
      | ~ l1_pre_topc(A_577)
      | ~ v2_pre_topc(A_577)
      | v2_struct_0(A_577) ) ),
    inference(resolution,[status(thm)],[c_369,c_371])).

tff(c_376,plain,(
    ! [C_580,B_582,A_577,E_579] :
      ( r1_tmap_1(C_580,B_582,k3_tmap_1(A_577,B_582,'#skF_4',C_580,E_579),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_582,E_579,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_580))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_580))
      | ~ m1_pre_topc(C_580,'#skF_4')
      | ~ m1_subset_1(E_579,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_582))))
      | ~ v1_funct_2(E_579,u1_struct_0('#skF_4'),u1_struct_0(B_582))
      | ~ v1_funct_1(E_579)
      | ~ m1_pre_topc('#skF_4',A_577)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_580,A_577)
      | v2_struct_0(C_580)
      | ~ l1_pre_topc(B_582)
      | ~ v2_pre_topc(B_582)
      | v2_struct_0(B_582)
      | ~ l1_pre_topc(A_577)
      | ~ v2_pre_topc(A_577)
      | v2_struct_0(A_577) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_65,c_373])).

tff(c_378,plain,(
    ! [C_583,B_584,A_585,E_586] :
      ( r1_tmap_1(C_583,B_584,k3_tmap_1(A_585,B_584,'#skF_4',C_583,E_586),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_584,E_586,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_583))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_583))
      | ~ m1_pre_topc(C_583,'#skF_4')
      | ~ m1_subset_1(E_586,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_584))))
      | ~ v1_funct_2(E_586,u1_struct_0('#skF_4'),u1_struct_0(B_584))
      | ~ v1_funct_1(E_586)
      | ~ m1_pre_topc('#skF_4',A_585)
      | ~ m1_pre_topc(C_583,A_585)
      | v2_struct_0(C_583)
      | ~ l1_pre_topc(B_584)
      | ~ v2_pre_topc(B_584)
      | v2_struct_0(B_584)
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_376])).

tff(c_380,plain,(
    ! [C_583,A_585] :
      ( r1_tmap_1(C_583,'#skF_2',k3_tmap_1(A_585,'#skF_2','#skF_4',C_583,'#skF_5'),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_583))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_583))
      | ~ m1_pre_topc(C_583,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_585)
      | ~ m1_pre_topc(C_583,A_585)
      | v2_struct_0(C_583)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(resolution,[status(thm)],[c_30,c_378])).

tff(c_383,plain,(
    ! [C_583,A_585] :
      ( r1_tmap_1(C_583,'#skF_2',k3_tmap_1(A_585,'#skF_2','#skF_4',C_583,'#skF_5'),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_583))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_583))
      | ~ m1_pre_topc(C_583,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_585)
      | ~ m1_pre_topc(C_583,A_585)
      | v2_struct_0(C_583)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_255,c_380])).

tff(c_385,plain,(
    ! [C_587,A_588] :
      ( r1_tmap_1(C_587,'#skF_2',k3_tmap_1(A_588,'#skF_2','#skF_4',C_587,'#skF_5'),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_587))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_587))
      | ~ m1_pre_topc(C_587,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_588)
      | ~ m1_pre_topc(C_587,A_588)
      | v2_struct_0(C_587)
      | ~ l1_pre_topc(A_588)
      | ~ v2_pre_topc(A_588)
      | v2_struct_0(A_588) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_383])).

tff(c_256,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_388,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_385,c_256])).

tff(c_391,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_36,c_28,c_22,c_16,c_388])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_42,c_391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.42  
% 2.93/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.43  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.93/1.43  
% 2.93/1.43  %Foreground sorts:
% 2.93/1.43  
% 2.93/1.43  
% 2.93/1.43  %Background operators:
% 2.93/1.43  
% 2.93/1.43  
% 2.93/1.43  %Foreground operators:
% 2.93/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.93/1.43  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.93/1.43  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.93/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.93/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.43  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.93/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.93/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.93/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.93/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.93/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.93/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.93/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.93/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.93/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.43  
% 2.93/1.45  tff(f_185, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 2.93/1.45  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.93/1.45  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.93/1.45  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.93/1.45  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 2.93/1.45  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_22, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_16, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_32, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_20, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_14, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_18, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_66, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 2.93/1.45  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_90, plain, (![B_525, A_526]: (v2_pre_topc(B_525) | ~m1_pre_topc(B_525, A_526) | ~l1_pre_topc(A_526) | ~v2_pre_topc(A_526))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.93/1.45  tff(c_99, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_90])).
% 2.93/1.45  tff(c_108, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_99])).
% 2.93/1.45  tff(c_71, plain, (![B_523, A_524]: (l1_pre_topc(B_523) | ~m1_pre_topc(B_523, A_524) | ~l1_pre_topc(A_524))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.45  tff(c_80, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_71])).
% 2.93/1.45  tff(c_87, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_80])).
% 2.93/1.45  tff(c_24, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_65, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 2.93/1.45  tff(c_205, plain, (![B_537, A_538, C_539]: (m1_connsp_2(B_537, A_538, C_539) | ~r2_hidden(C_539, B_537) | ~v3_pre_topc(B_537, A_538) | ~m1_subset_1(C_539, u1_struct_0(A_538)) | ~m1_subset_1(B_537, k1_zfmisc_1(u1_struct_0(A_538))) | ~l1_pre_topc(A_538) | ~v2_pre_topc(A_538) | v2_struct_0(A_538))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.93/1.45  tff(c_207, plain, (![B_537]: (m1_connsp_2(B_537, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_537) | ~v3_pre_topc(B_537, '#skF_4') | ~m1_subset_1(B_537, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_65, c_205])).
% 2.93/1.45  tff(c_212, plain, (![B_537]: (m1_connsp_2(B_537, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_537) | ~v3_pre_topc(B_537, '#skF_4') | ~m1_subset_1(B_537, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_87, c_207])).
% 2.93/1.45  tff(c_218, plain, (![B_540]: (m1_connsp_2(B_540, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_540) | ~v3_pre_topc(B_540, '#skF_4') | ~m1_subset_1(B_540, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_212])).
% 2.93/1.45  tff(c_221, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_218])).
% 2.93/1.45  tff(c_224, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66, c_221])).
% 2.93/1.45  tff(c_62, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_63, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_62])).
% 2.93/1.45  tff(c_111, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_63])).
% 2.93/1.45  tff(c_56, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_64, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_56])).
% 2.93/1.45  tff(c_152, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_64])).
% 2.93/1.45  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 2.93/1.45  tff(c_240, plain, (![D_555, F_553, H_558, B_559, E_556, C_557, A_554]: (r1_tmap_1(D_555, B_559, E_556, H_558) | ~r1_tmap_1(C_557, B_559, k3_tmap_1(A_554, B_559, D_555, C_557, E_556), H_558) | ~m1_connsp_2(F_553, D_555, H_558) | ~r1_tarski(F_553, u1_struct_0(C_557)) | ~m1_subset_1(H_558, u1_struct_0(C_557)) | ~m1_subset_1(H_558, u1_struct_0(D_555)) | ~m1_subset_1(F_553, k1_zfmisc_1(u1_struct_0(D_555))) | ~m1_pre_topc(C_557, D_555) | ~m1_subset_1(E_556, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_555), u1_struct_0(B_559)))) | ~v1_funct_2(E_556, u1_struct_0(D_555), u1_struct_0(B_559)) | ~v1_funct_1(E_556) | ~m1_pre_topc(D_555, A_554) | v2_struct_0(D_555) | ~m1_pre_topc(C_557, A_554) | v2_struct_0(C_557) | ~l1_pre_topc(B_559) | ~v2_pre_topc(B_559) | v2_struct_0(B_559) | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554) | v2_struct_0(A_554))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.93/1.45  tff(c_242, plain, (![F_553]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(F_553, '#skF_4', '#skF_8') | ~r1_tarski(F_553, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_553, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_111, c_240])).
% 2.93/1.45  tff(c_245, plain, (![F_553]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(F_553, '#skF_4', '#skF_8') | ~r1_tarski(F_553, u1_struct_0('#skF_3')) | ~m1_subset_1(F_553, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_40, c_36, c_34, c_32, c_30, c_28, c_65, c_22, c_242])).
% 2.93/1.45  tff(c_247, plain, (![F_560]: (~m1_connsp_2(F_560, '#skF_4', '#skF_8') | ~r1_tarski(F_560, u1_struct_0('#skF_3')) | ~m1_subset_1(F_560, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_42, c_38, c_152, c_245])).
% 2.93/1.45  tff(c_250, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_247])).
% 2.93/1.45  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_224, c_250])).
% 2.93/1.45  tff(c_255, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_63])).
% 2.93/1.45  tff(c_350, plain, (![B_571, A_572, C_573]: (m1_connsp_2(B_571, A_572, C_573) | ~r2_hidden(C_573, B_571) | ~v3_pre_topc(B_571, A_572) | ~m1_subset_1(C_573, u1_struct_0(A_572)) | ~m1_subset_1(B_571, k1_zfmisc_1(u1_struct_0(A_572))) | ~l1_pre_topc(A_572) | ~v2_pre_topc(A_572) | v2_struct_0(A_572))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.93/1.45  tff(c_352, plain, (![B_571]: (m1_connsp_2(B_571, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_571) | ~v3_pre_topc(B_571, '#skF_4') | ~m1_subset_1(B_571, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_65, c_350])).
% 2.93/1.45  tff(c_357, plain, (![B_571]: (m1_connsp_2(B_571, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_571) | ~v3_pre_topc(B_571, '#skF_4') | ~m1_subset_1(B_571, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_87, c_352])).
% 2.93/1.45  tff(c_363, plain, (![B_574]: (m1_connsp_2(B_574, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_574) | ~v3_pre_topc(B_574, '#skF_4') | ~m1_subset_1(B_574, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_357])).
% 2.93/1.45  tff(c_366, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_363])).
% 2.93/1.45  tff(c_369, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66, c_366])).
% 2.93/1.45  tff(c_371, plain, (![F_576, D_578, A_577, C_580, B_582, E_579, H_581]: (r1_tmap_1(C_580, B_582, k3_tmap_1(A_577, B_582, D_578, C_580, E_579), H_581) | ~r1_tmap_1(D_578, B_582, E_579, H_581) | ~m1_connsp_2(F_576, D_578, H_581) | ~r1_tarski(F_576, u1_struct_0(C_580)) | ~m1_subset_1(H_581, u1_struct_0(C_580)) | ~m1_subset_1(H_581, u1_struct_0(D_578)) | ~m1_subset_1(F_576, k1_zfmisc_1(u1_struct_0(D_578))) | ~m1_pre_topc(C_580, D_578) | ~m1_subset_1(E_579, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_578), u1_struct_0(B_582)))) | ~v1_funct_2(E_579, u1_struct_0(D_578), u1_struct_0(B_582)) | ~v1_funct_1(E_579) | ~m1_pre_topc(D_578, A_577) | v2_struct_0(D_578) | ~m1_pre_topc(C_580, A_577) | v2_struct_0(C_580) | ~l1_pre_topc(B_582) | ~v2_pre_topc(B_582) | v2_struct_0(B_582) | ~l1_pre_topc(A_577) | ~v2_pre_topc(A_577) | v2_struct_0(A_577))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.93/1.45  tff(c_373, plain, (![C_580, B_582, A_577, E_579]: (r1_tmap_1(C_580, B_582, k3_tmap_1(A_577, B_582, '#skF_4', C_580, E_579), '#skF_8') | ~r1_tmap_1('#skF_4', B_582, E_579, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_580)) | ~m1_subset_1('#skF_8', u1_struct_0(C_580)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(C_580, '#skF_4') | ~m1_subset_1(E_579, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_582)))) | ~v1_funct_2(E_579, u1_struct_0('#skF_4'), u1_struct_0(B_582)) | ~v1_funct_1(E_579) | ~m1_pre_topc('#skF_4', A_577) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_580, A_577) | v2_struct_0(C_580) | ~l1_pre_topc(B_582) | ~v2_pre_topc(B_582) | v2_struct_0(B_582) | ~l1_pre_topc(A_577) | ~v2_pre_topc(A_577) | v2_struct_0(A_577))), inference(resolution, [status(thm)], [c_369, c_371])).
% 2.93/1.45  tff(c_376, plain, (![C_580, B_582, A_577, E_579]: (r1_tmap_1(C_580, B_582, k3_tmap_1(A_577, B_582, '#skF_4', C_580, E_579), '#skF_8') | ~r1_tmap_1('#skF_4', B_582, E_579, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_580)) | ~m1_subset_1('#skF_8', u1_struct_0(C_580)) | ~m1_pre_topc(C_580, '#skF_4') | ~m1_subset_1(E_579, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_582)))) | ~v1_funct_2(E_579, u1_struct_0('#skF_4'), u1_struct_0(B_582)) | ~v1_funct_1(E_579) | ~m1_pre_topc('#skF_4', A_577) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_580, A_577) | v2_struct_0(C_580) | ~l1_pre_topc(B_582) | ~v2_pre_topc(B_582) | v2_struct_0(B_582) | ~l1_pre_topc(A_577) | ~v2_pre_topc(A_577) | v2_struct_0(A_577))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_65, c_373])).
% 2.93/1.45  tff(c_378, plain, (![C_583, B_584, A_585, E_586]: (r1_tmap_1(C_583, B_584, k3_tmap_1(A_585, B_584, '#skF_4', C_583, E_586), '#skF_8') | ~r1_tmap_1('#skF_4', B_584, E_586, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_583)) | ~m1_subset_1('#skF_8', u1_struct_0(C_583)) | ~m1_pre_topc(C_583, '#skF_4') | ~m1_subset_1(E_586, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_584)))) | ~v1_funct_2(E_586, u1_struct_0('#skF_4'), u1_struct_0(B_584)) | ~v1_funct_1(E_586) | ~m1_pre_topc('#skF_4', A_585) | ~m1_pre_topc(C_583, A_585) | v2_struct_0(C_583) | ~l1_pre_topc(B_584) | ~v2_pre_topc(B_584) | v2_struct_0(B_584) | ~l1_pre_topc(A_585) | ~v2_pre_topc(A_585) | v2_struct_0(A_585))), inference(negUnitSimplification, [status(thm)], [c_38, c_376])).
% 2.93/1.45  tff(c_380, plain, (![C_583, A_585]: (r1_tmap_1(C_583, '#skF_2', k3_tmap_1(A_585, '#skF_2', '#skF_4', C_583, '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_583)) | ~m1_subset_1('#skF_8', u1_struct_0(C_583)) | ~m1_pre_topc(C_583, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_585) | ~m1_pre_topc(C_583, A_585) | v2_struct_0(C_583) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_585) | ~v2_pre_topc(A_585) | v2_struct_0(A_585))), inference(resolution, [status(thm)], [c_30, c_378])).
% 2.93/1.45  tff(c_383, plain, (![C_583, A_585]: (r1_tmap_1(C_583, '#skF_2', k3_tmap_1(A_585, '#skF_2', '#skF_4', C_583, '#skF_5'), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_583)) | ~m1_subset_1('#skF_8', u1_struct_0(C_583)) | ~m1_pre_topc(C_583, '#skF_4') | ~m1_pre_topc('#skF_4', A_585) | ~m1_pre_topc(C_583, A_585) | v2_struct_0(C_583) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_585) | ~v2_pre_topc(A_585) | v2_struct_0(A_585))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_32, c_255, c_380])).
% 2.93/1.45  tff(c_385, plain, (![C_587, A_588]: (r1_tmap_1(C_587, '#skF_2', k3_tmap_1(A_588, '#skF_2', '#skF_4', C_587, '#skF_5'), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_587)) | ~m1_subset_1('#skF_8', u1_struct_0(C_587)) | ~m1_pre_topc(C_587, '#skF_4') | ~m1_pre_topc('#skF_4', A_588) | ~m1_pre_topc(C_587, A_588) | v2_struct_0(C_587) | ~l1_pre_topc(A_588) | ~v2_pre_topc(A_588) | v2_struct_0(A_588))), inference(negUnitSimplification, [status(thm)], [c_48, c_383])).
% 2.93/1.45  tff(c_256, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_63])).
% 2.93/1.45  tff(c_388, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_385, c_256])).
% 2.93/1.45  tff(c_391, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_36, c_28, c_22, c_16, c_388])).
% 2.93/1.45  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_42, c_391])).
% 2.93/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.45  
% 2.93/1.45  Inference rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Ref     : 0
% 2.93/1.45  #Sup     : 59
% 2.93/1.45  #Fact    : 0
% 2.93/1.45  #Define  : 0
% 2.93/1.45  #Split   : 1
% 2.93/1.45  #Chain   : 0
% 2.93/1.45  #Close   : 0
% 2.93/1.45  
% 2.93/1.45  Ordering : KBO
% 2.93/1.45  
% 2.93/1.45  Simplification rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Subsume      : 10
% 2.93/1.45  #Demod        : 147
% 2.93/1.45  #Tautology    : 26
% 2.93/1.45  #SimpNegUnit  : 10
% 2.93/1.45  #BackRed      : 0
% 2.93/1.45  
% 2.93/1.45  #Partial instantiations: 0
% 2.93/1.45  #Strategies tried      : 1
% 2.93/1.45  
% 2.93/1.45  Timing (in seconds)
% 2.93/1.45  ----------------------
% 2.93/1.45  Preprocessing        : 0.37
% 2.93/1.45  Parsing              : 0.17
% 2.93/1.45  CNF conversion       : 0.07
% 2.93/1.45  Main loop            : 0.28
% 2.93/1.45  Inferencing          : 0.10
% 2.93/1.45  Reduction            : 0.09
% 2.93/1.45  Demodulation         : 0.07
% 2.93/1.45  BG Simplification    : 0.02
% 2.93/1.45  Subsumption          : 0.05
% 2.93/1.45  Abstraction          : 0.01
% 2.93/1.45  MUC search           : 0.00
% 2.93/1.45  Cooper               : 0.00
% 2.93/1.45  Total                : 0.69
% 2.93/1.45  Index Insertion      : 0.00
% 2.93/1.45  Index Deletion       : 0.00
% 2.93/1.45  Index Matching       : 0.00
% 2.93/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
