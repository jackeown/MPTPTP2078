%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:22 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 187 expanded)
%              Number of leaves         :   35 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  297 (1630 expanded)
%              Number of equality atoms :    5 (  67 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_232,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_174,axiom,(
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

tff(f_119,axiom,(
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

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_28,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_36,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_79,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_30,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_117,plain,(
    ! [B_665,A_666] :
      ( v2_pre_topc(B_665)
      | ~ m1_pre_topc(B_665,A_666)
      | ~ l1_pre_topc(A_666)
      | ~ v2_pre_topc(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_123,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_117])).

tff(c_132,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_123])).

tff(c_86,plain,(
    ! [B_661,A_662] :
      ( l1_pre_topc(B_661)
      | ~ m1_pre_topc(B_661,A_662)
      | ~ l1_pre_topc(A_662) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_101,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_92])).

tff(c_34,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_32,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_177,plain,(
    ! [C_683,A_684,B_685,D_686] :
      ( m1_connsp_2(C_683,A_684,B_685)
      | ~ r2_hidden(B_685,D_686)
      | ~ r1_tarski(D_686,C_683)
      | ~ v3_pre_topc(D_686,A_684)
      | ~ m1_subset_1(D_686,k1_zfmisc_1(u1_struct_0(A_684)))
      | ~ m1_subset_1(C_683,k1_zfmisc_1(u1_struct_0(A_684)))
      | ~ m1_subset_1(B_685,u1_struct_0(A_684))
      | ~ l1_pre_topc(A_684)
      | ~ v2_pre_topc(A_684)
      | v2_struct_0(A_684) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_191,plain,(
    ! [C_693,A_694] :
      ( m1_connsp_2(C_693,A_694,'#skF_8')
      | ~ r1_tarski('#skF_7',C_693)
      | ~ v3_pre_topc('#skF_7',A_694)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_694)))
      | ~ m1_subset_1(C_693,k1_zfmisc_1(u1_struct_0(A_694)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_694))
      | ~ l1_pre_topc(A_694)
      | ~ v2_pre_topc(A_694)
      | v2_struct_0(A_694) ) ),
    inference(resolution,[status(thm)],[c_32,c_177])).

tff(c_193,plain,(
    ! [C_693] :
      ( m1_connsp_2(C_693,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_693)
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(C_693,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_191])).

tff(c_196,plain,(
    ! [C_693] :
      ( m1_connsp_2(C_693,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_693)
      | ~ m1_subset_1(C_693,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_101,c_38,c_34,c_193])).

tff(c_198,plain,(
    ! [C_695] :
      ( m1_connsp_2(C_695,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_695)
      | ~ m1_subset_1(C_695,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_196])).

tff(c_205,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_198])).

tff(c_212,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_205])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_116,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_46,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_138,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_77])).

tff(c_235,plain,(
    ! [F_719,A_715,D_720,H_717,C_716,E_714,B_718] :
      ( r1_tmap_1(D_720,B_718,E_714,H_717)
      | ~ r1_tmap_1(C_716,B_718,k3_tmap_1(A_715,B_718,D_720,C_716,E_714),H_717)
      | ~ m1_connsp_2(F_719,D_720,H_717)
      | ~ r1_tarski(F_719,u1_struct_0(C_716))
      | ~ m1_subset_1(H_717,u1_struct_0(C_716))
      | ~ m1_subset_1(H_717,u1_struct_0(D_720))
      | ~ m1_subset_1(F_719,k1_zfmisc_1(u1_struct_0(D_720)))
      | ~ m1_pre_topc(C_716,D_720)
      | ~ m1_subset_1(E_714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_720),u1_struct_0(B_718))))
      | ~ v1_funct_2(E_714,u1_struct_0(D_720),u1_struct_0(B_718))
      | ~ v1_funct_1(E_714)
      | ~ m1_pre_topc(D_720,A_715)
      | v2_struct_0(D_720)
      | ~ m1_pre_topc(C_716,A_715)
      | v2_struct_0(C_716)
      | ~ l1_pre_topc(B_718)
      | ~ v2_pre_topc(B_718)
      | v2_struct_0(B_718)
      | ~ l1_pre_topc(A_715)
      | ~ v2_pre_topc(A_715)
      | v2_struct_0(A_715) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_239,plain,(
    ! [F_719] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_719,'#skF_5','#skF_8')
      | ~ r1_tarski(F_719,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_719,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_138,c_235])).

tff(c_246,plain,(
    ! [F_719] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_719,'#skF_5','#skF_8')
      | ~ r1_tarski(F_719,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_719,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_54,c_50,c_48,c_46,c_44,c_42,c_38,c_79,c_239])).

tff(c_248,plain,(
    ! [F_721] :
      ( ~ m1_connsp_2(F_721,'#skF_5','#skF_8')
      | ~ r1_tarski(F_721,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_721,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_56,c_52,c_116,c_246])).

tff(c_255,plain,
    ( ~ m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_248])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_212,c_255])).

tff(c_265,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_355,plain,(
    ! [B_751,G_752,D_748,E_747,C_750,A_749] :
      ( r1_tmap_1(D_748,B_751,k3_tmap_1(A_749,B_751,C_750,D_748,E_747),G_752)
      | ~ r1_tmap_1(C_750,B_751,E_747,G_752)
      | ~ m1_pre_topc(D_748,C_750)
      | ~ m1_subset_1(G_752,u1_struct_0(D_748))
      | ~ m1_subset_1(G_752,u1_struct_0(C_750))
      | ~ m1_subset_1(E_747,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_750),u1_struct_0(B_751))))
      | ~ v1_funct_2(E_747,u1_struct_0(C_750),u1_struct_0(B_751))
      | ~ v1_funct_1(E_747)
      | ~ m1_pre_topc(D_748,A_749)
      | v2_struct_0(D_748)
      | ~ m1_pre_topc(C_750,A_749)
      | v2_struct_0(C_750)
      | ~ l1_pre_topc(B_751)
      | ~ v2_pre_topc(B_751)
      | v2_struct_0(B_751)
      | ~ l1_pre_topc(A_749)
      | ~ v2_pre_topc(A_749)
      | v2_struct_0(A_749) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_357,plain,(
    ! [D_748,A_749,G_752] :
      ( r1_tmap_1(D_748,'#skF_3',k3_tmap_1(A_749,'#skF_3','#skF_5',D_748,'#skF_6'),G_752)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_752)
      | ~ m1_pre_topc(D_748,'#skF_5')
      | ~ m1_subset_1(G_752,u1_struct_0(D_748))
      | ~ m1_subset_1(G_752,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_748,A_749)
      | v2_struct_0(D_748)
      | ~ m1_pre_topc('#skF_5',A_749)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_749)
      | ~ v2_pre_topc(A_749)
      | v2_struct_0(A_749) ) ),
    inference(resolution,[status(thm)],[c_44,c_355])).

tff(c_360,plain,(
    ! [D_748,A_749,G_752] :
      ( r1_tmap_1(D_748,'#skF_3',k3_tmap_1(A_749,'#skF_3','#skF_5',D_748,'#skF_6'),G_752)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_752)
      | ~ m1_pre_topc(D_748,'#skF_5')
      | ~ m1_subset_1(G_752,u1_struct_0(D_748))
      | ~ m1_subset_1(G_752,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_748,A_749)
      | v2_struct_0(D_748)
      | ~ m1_pre_topc('#skF_5',A_749)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_749)
      | ~ v2_pre_topc(A_749)
      | v2_struct_0(A_749) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_357])).

tff(c_374,plain,(
    ! [D_756,A_757,G_758] :
      ( r1_tmap_1(D_756,'#skF_3',k3_tmap_1(A_757,'#skF_3','#skF_5',D_756,'#skF_6'),G_758)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_758)
      | ~ m1_pre_topc(D_756,'#skF_5')
      | ~ m1_subset_1(G_758,u1_struct_0(D_756))
      | ~ m1_subset_1(G_758,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_756,A_757)
      | v2_struct_0(D_756)
      | ~ m1_pre_topc('#skF_5',A_757)
      | ~ l1_pre_topc(A_757)
      | ~ v2_pre_topc(A_757)
      | v2_struct_0(A_757) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_360])).

tff(c_264,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_377,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_374,c_264])).

tff(c_380,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_38,c_79,c_42,c_265,c_377])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_56,c_380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:31:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.45  
% 3.38/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.45  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 3.38/1.45  
% 3.38/1.45  %Foreground sorts:
% 3.38/1.45  
% 3.38/1.45  
% 3.38/1.45  %Background operators:
% 3.38/1.45  
% 3.38/1.45  
% 3.38/1.45  %Foreground operators:
% 3.38/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.38/1.45  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.38/1.45  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.38/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.38/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.38/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.45  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.38/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.38/1.45  tff('#skF_7', type, '#skF_7': $i).
% 3.38/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.38/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.45  tff('#skF_9', type, '#skF_9': $i).
% 3.38/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.45  tff('#skF_8', type, '#skF_8': $i).
% 3.38/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.38/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.38/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.38/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.45  
% 3.49/1.47  tff(f_232, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.49/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.49/1.47  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.49/1.47  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.49/1.47  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 3.49/1.47  tff(f_174, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.49/1.47  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.49/1.47  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_50, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_38, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_28, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_36, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_79, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36])).
% 3.49/1.47  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_30, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.47  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_117, plain, (![B_665, A_666]: (v2_pre_topc(B_665) | ~m1_pre_topc(B_665, A_666) | ~l1_pre_topc(A_666) | ~v2_pre_topc(A_666))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.49/1.47  tff(c_123, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_117])).
% 3.49/1.47  tff(c_132, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_123])).
% 3.49/1.47  tff(c_86, plain, (![B_661, A_662]: (l1_pre_topc(B_661) | ~m1_pre_topc(B_661, A_662) | ~l1_pre_topc(A_662))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.47  tff(c_92, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_86])).
% 3.49/1.47  tff(c_101, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_92])).
% 3.49/1.47  tff(c_34, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_32, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_177, plain, (![C_683, A_684, B_685, D_686]: (m1_connsp_2(C_683, A_684, B_685) | ~r2_hidden(B_685, D_686) | ~r1_tarski(D_686, C_683) | ~v3_pre_topc(D_686, A_684) | ~m1_subset_1(D_686, k1_zfmisc_1(u1_struct_0(A_684))) | ~m1_subset_1(C_683, k1_zfmisc_1(u1_struct_0(A_684))) | ~m1_subset_1(B_685, u1_struct_0(A_684)) | ~l1_pre_topc(A_684) | ~v2_pre_topc(A_684) | v2_struct_0(A_684))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.49/1.47  tff(c_191, plain, (![C_693, A_694]: (m1_connsp_2(C_693, A_694, '#skF_8') | ~r1_tarski('#skF_7', C_693) | ~v3_pre_topc('#skF_7', A_694) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_694))) | ~m1_subset_1(C_693, k1_zfmisc_1(u1_struct_0(A_694))) | ~m1_subset_1('#skF_8', u1_struct_0(A_694)) | ~l1_pre_topc(A_694) | ~v2_pre_topc(A_694) | v2_struct_0(A_694))), inference(resolution, [status(thm)], [c_32, c_177])).
% 3.49/1.47  tff(c_193, plain, (![C_693]: (m1_connsp_2(C_693, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_693) | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(C_693, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_191])).
% 3.49/1.47  tff(c_196, plain, (![C_693]: (m1_connsp_2(C_693, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_693) | ~m1_subset_1(C_693, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_101, c_38, c_34, c_193])).
% 3.49/1.47  tff(c_198, plain, (![C_695]: (m1_connsp_2(C_695, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_695) | ~m1_subset_1(C_695, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_196])).
% 3.49/1.47  tff(c_205, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_40, c_198])).
% 3.49/1.47  tff(c_212, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_205])).
% 3.49/1.47  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_70, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_78, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 3.49/1.47  tff(c_116, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 3.49/1.47  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_46, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_76, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_232])).
% 3.49/1.47  tff(c_77, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_76])).
% 3.49/1.47  tff(c_138, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_116, c_77])).
% 3.49/1.47  tff(c_235, plain, (![F_719, A_715, D_720, H_717, C_716, E_714, B_718]: (r1_tmap_1(D_720, B_718, E_714, H_717) | ~r1_tmap_1(C_716, B_718, k3_tmap_1(A_715, B_718, D_720, C_716, E_714), H_717) | ~m1_connsp_2(F_719, D_720, H_717) | ~r1_tarski(F_719, u1_struct_0(C_716)) | ~m1_subset_1(H_717, u1_struct_0(C_716)) | ~m1_subset_1(H_717, u1_struct_0(D_720)) | ~m1_subset_1(F_719, k1_zfmisc_1(u1_struct_0(D_720))) | ~m1_pre_topc(C_716, D_720) | ~m1_subset_1(E_714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_720), u1_struct_0(B_718)))) | ~v1_funct_2(E_714, u1_struct_0(D_720), u1_struct_0(B_718)) | ~v1_funct_1(E_714) | ~m1_pre_topc(D_720, A_715) | v2_struct_0(D_720) | ~m1_pre_topc(C_716, A_715) | v2_struct_0(C_716) | ~l1_pre_topc(B_718) | ~v2_pre_topc(B_718) | v2_struct_0(B_718) | ~l1_pre_topc(A_715) | ~v2_pre_topc(A_715) | v2_struct_0(A_715))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.49/1.47  tff(c_239, plain, (![F_719]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_719, '#skF_5', '#skF_8') | ~r1_tarski(F_719, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_719, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_138, c_235])).
% 3.49/1.47  tff(c_246, plain, (![F_719]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_719, '#skF_5', '#skF_8') | ~r1_tarski(F_719, u1_struct_0('#skF_4')) | ~m1_subset_1(F_719, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_54, c_50, c_48, c_46, c_44, c_42, c_38, c_79, c_239])).
% 3.49/1.47  tff(c_248, plain, (![F_721]: (~m1_connsp_2(F_721, '#skF_5', '#skF_8') | ~r1_tarski(F_721, u1_struct_0('#skF_4')) | ~m1_subset_1(F_721, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_56, c_52, c_116, c_246])).
% 3.49/1.47  tff(c_255, plain, (~m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_248])).
% 3.49/1.47  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_212, c_255])).
% 3.49/1.47  tff(c_265, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 3.49/1.47  tff(c_355, plain, (![B_751, G_752, D_748, E_747, C_750, A_749]: (r1_tmap_1(D_748, B_751, k3_tmap_1(A_749, B_751, C_750, D_748, E_747), G_752) | ~r1_tmap_1(C_750, B_751, E_747, G_752) | ~m1_pre_topc(D_748, C_750) | ~m1_subset_1(G_752, u1_struct_0(D_748)) | ~m1_subset_1(G_752, u1_struct_0(C_750)) | ~m1_subset_1(E_747, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_750), u1_struct_0(B_751)))) | ~v1_funct_2(E_747, u1_struct_0(C_750), u1_struct_0(B_751)) | ~v1_funct_1(E_747) | ~m1_pre_topc(D_748, A_749) | v2_struct_0(D_748) | ~m1_pre_topc(C_750, A_749) | v2_struct_0(C_750) | ~l1_pre_topc(B_751) | ~v2_pre_topc(B_751) | v2_struct_0(B_751) | ~l1_pre_topc(A_749) | ~v2_pre_topc(A_749) | v2_struct_0(A_749))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.49/1.47  tff(c_357, plain, (![D_748, A_749, G_752]: (r1_tmap_1(D_748, '#skF_3', k3_tmap_1(A_749, '#skF_3', '#skF_5', D_748, '#skF_6'), G_752) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_752) | ~m1_pre_topc(D_748, '#skF_5') | ~m1_subset_1(G_752, u1_struct_0(D_748)) | ~m1_subset_1(G_752, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_748, A_749) | v2_struct_0(D_748) | ~m1_pre_topc('#skF_5', A_749) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_749) | ~v2_pre_topc(A_749) | v2_struct_0(A_749))), inference(resolution, [status(thm)], [c_44, c_355])).
% 3.49/1.47  tff(c_360, plain, (![D_748, A_749, G_752]: (r1_tmap_1(D_748, '#skF_3', k3_tmap_1(A_749, '#skF_3', '#skF_5', D_748, '#skF_6'), G_752) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_752) | ~m1_pre_topc(D_748, '#skF_5') | ~m1_subset_1(G_752, u1_struct_0(D_748)) | ~m1_subset_1(G_752, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_748, A_749) | v2_struct_0(D_748) | ~m1_pre_topc('#skF_5', A_749) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_749) | ~v2_pre_topc(A_749) | v2_struct_0(A_749))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_357])).
% 3.49/1.47  tff(c_374, plain, (![D_756, A_757, G_758]: (r1_tmap_1(D_756, '#skF_3', k3_tmap_1(A_757, '#skF_3', '#skF_5', D_756, '#skF_6'), G_758) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_758) | ~m1_pre_topc(D_756, '#skF_5') | ~m1_subset_1(G_758, u1_struct_0(D_756)) | ~m1_subset_1(G_758, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_756, A_757) | v2_struct_0(D_756) | ~m1_pre_topc('#skF_5', A_757) | ~l1_pre_topc(A_757) | ~v2_pre_topc(A_757) | v2_struct_0(A_757))), inference(negUnitSimplification, [status(thm)], [c_62, c_52, c_360])).
% 3.49/1.47  tff(c_264, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 3.49/1.47  tff(c_377, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_374, c_264])).
% 3.49/1.47  tff(c_380, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_38, c_79, c_42, c_265, c_377])).
% 3.49/1.47  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_56, c_380])).
% 3.49/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.47  
% 3.49/1.47  Inference rules
% 3.49/1.47  ----------------------
% 3.49/1.47  #Ref     : 0
% 3.49/1.47  #Sup     : 50
% 3.49/1.47  #Fact    : 0
% 3.49/1.47  #Define  : 0
% 3.49/1.47  #Split   : 2
% 3.49/1.47  #Chain   : 0
% 3.49/1.47  #Close   : 0
% 3.49/1.47  
% 3.49/1.47  Ordering : KBO
% 3.49/1.47  
% 3.49/1.47  Simplification rules
% 3.49/1.47  ----------------------
% 3.49/1.47  #Subsume      : 1
% 3.49/1.47  #Demod        : 91
% 3.49/1.47  #Tautology    : 11
% 3.49/1.47  #SimpNegUnit  : 19
% 3.49/1.47  #BackRed      : 0
% 3.49/1.47  
% 3.49/1.47  #Partial instantiations: 0
% 3.49/1.47  #Strategies tried      : 1
% 3.49/1.47  
% 3.49/1.47  Timing (in seconds)
% 3.49/1.47  ----------------------
% 3.49/1.48  Preprocessing        : 0.39
% 3.49/1.48  Parsing              : 0.18
% 3.49/1.48  CNF conversion       : 0.07
% 3.49/1.48  Main loop            : 0.30
% 3.49/1.48  Inferencing          : 0.11
% 3.49/1.48  Reduction            : 0.09
% 3.49/1.48  Demodulation         : 0.07
% 3.49/1.48  BG Simplification    : 0.02
% 3.49/1.48  Subsumption          : 0.06
% 3.49/1.48  Abstraction          : 0.01
% 3.49/1.48  MUC search           : 0.00
% 3.49/1.48  Cooper               : 0.00
% 3.49/1.48  Total                : 0.72
% 3.49/1.48  Index Insertion      : 0.00
% 3.49/1.48  Index Deletion       : 0.00
% 3.49/1.48  Index Matching       : 0.00
% 3.49/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
