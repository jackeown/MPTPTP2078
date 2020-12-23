%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:23 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 233 expanded)
%              Number of leaves         :   37 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          :  339 (1882 expanded)
%              Number of equality atoms :    4 (  73 expanded)
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

tff(f_253,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_69,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_195,axiom,(
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

tff(f_140,axiom,(
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
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_32,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_40,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_83,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_99,plain,(
    ! [B_676,A_677] :
      ( l1_pre_topc(B_676)
      | ~ m1_pre_topc(B_676,A_677)
      | ~ l1_pre_topc(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_99])).

tff(c_116,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_108])).

tff(c_22,plain,(
    ! [A_34] :
      ( m1_pre_topc(A_34,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_111,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_99])).

tff(c_119,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_111])).

tff(c_20,plain,(
    ! [B_33,A_31] :
      ( m1_subset_1(u1_struct_0(B_33),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_126,plain,(
    ! [B_678,A_679] :
      ( v2_pre_topc(B_678)
      | ~ m1_pre_topc(B_678,A_679)
      | ~ l1_pre_topc(A_679)
      | ~ v2_pre_topc(A_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_138,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_148,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_138])).

tff(c_38,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_36,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_303,plain,(
    ! [C_725,A_726,B_727,D_728] :
      ( m1_connsp_2(C_725,A_726,B_727)
      | ~ r2_hidden(B_727,D_728)
      | ~ r1_tarski(D_728,C_725)
      | ~ v3_pre_topc(D_728,A_726)
      | ~ m1_subset_1(D_728,k1_zfmisc_1(u1_struct_0(A_726)))
      | ~ m1_subset_1(C_725,k1_zfmisc_1(u1_struct_0(A_726)))
      | ~ m1_subset_1(B_727,u1_struct_0(A_726))
      | ~ l1_pre_topc(A_726)
      | ~ v2_pre_topc(A_726)
      | v2_struct_0(A_726) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_317,plain,(
    ! [C_732,A_733] :
      ( m1_connsp_2(C_732,A_733,'#skF_8')
      | ~ r1_tarski('#skF_7',C_732)
      | ~ v3_pre_topc('#skF_7',A_733)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_733)))
      | ~ m1_subset_1(C_732,k1_zfmisc_1(u1_struct_0(A_733)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_733))
      | ~ l1_pre_topc(A_733)
      | ~ v2_pre_topc(A_733)
      | v2_struct_0(A_733) ) ),
    inference(resolution,[status(thm)],[c_36,c_303])).

tff(c_322,plain,(
    ! [C_732] :
      ( m1_connsp_2(C_732,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_732)
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(C_732,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_317])).

tff(c_326,plain,(
    ! [C_732] :
      ( m1_connsp_2(C_732,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_732)
      | ~ m1_subset_1(C_732,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_119,c_42,c_38,c_322])).

tff(c_328,plain,(
    ! [C_734] :
      ( m1_connsp_2(C_734,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_734)
      | ~ m1_subset_1(C_734,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_326])).

tff(c_336,plain,(
    ! [B_33] :
      ( m1_connsp_2(u1_struct_0(B_33),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_33))
      | ~ m1_pre_topc(B_33,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_328])).

tff(c_350,plain,(
    ! [B_33] :
      ( m1_connsp_2(u1_struct_0(B_33),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_33))
      | ~ m1_pre_topc(B_33,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_336])).

tff(c_151,plain,(
    ! [B_680,A_681] :
      ( m1_subset_1(u1_struct_0(B_680),k1_zfmisc_1(u1_struct_0(A_681)))
      | ~ m1_pre_topc(B_680,A_681)
      | ~ l1_pre_topc(A_681) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_155,plain,(
    ! [B_680,A_681] :
      ( r1_tarski(u1_struct_0(B_680),u1_struct_0(A_681))
      | ~ m1_pre_topc(B_680,A_681)
      | ~ l1_pre_topc(A_681) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_81,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_80])).

tff(c_210,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_74])).

tff(c_212,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_82])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_50,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_441,plain,(
    ! [H_756,C_757,E_758,D_755,F_754,A_752,B_753] :
      ( r1_tmap_1(D_755,B_753,E_758,H_756)
      | ~ r1_tmap_1(C_757,B_753,k3_tmap_1(A_752,B_753,D_755,C_757,E_758),H_756)
      | ~ m1_connsp_2(F_754,D_755,H_756)
      | ~ r1_tarski(F_754,u1_struct_0(C_757))
      | ~ m1_subset_1(H_756,u1_struct_0(C_757))
      | ~ m1_subset_1(H_756,u1_struct_0(D_755))
      | ~ m1_subset_1(F_754,k1_zfmisc_1(u1_struct_0(D_755)))
      | ~ m1_pre_topc(C_757,D_755)
      | ~ m1_subset_1(E_758,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_755),u1_struct_0(B_753))))
      | ~ v1_funct_2(E_758,u1_struct_0(D_755),u1_struct_0(B_753))
      | ~ v1_funct_1(E_758)
      | ~ m1_pre_topc(D_755,A_752)
      | v2_struct_0(D_755)
      | ~ m1_pre_topc(C_757,A_752)
      | v2_struct_0(C_757)
      | ~ l1_pre_topc(B_753)
      | ~ v2_pre_topc(B_753)
      | v2_struct_0(B_753)
      | ~ l1_pre_topc(A_752)
      | ~ v2_pre_topc(A_752)
      | v2_struct_0(A_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_443,plain,(
    ! [F_754] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_754,'#skF_5','#skF_8')
      | ~ r1_tarski(F_754,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_754,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_210,c_441])).

tff(c_446,plain,(
    ! [F_754] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_754,'#skF_5','#skF_8')
      | ~ r1_tarski(F_754,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_754,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_50,c_48,c_46,c_42,c_83,c_443])).

tff(c_448,plain,(
    ! [F_759] :
      ( ~ m1_connsp_2(F_759,'#skF_5','#skF_8')
      | ~ r1_tarski(F_759,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_759,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_212,c_446])).

tff(c_456,plain,(
    ! [B_33] :
      ( ~ m1_connsp_2(u1_struct_0(B_33),'#skF_5','#skF_8')
      | ~ r1_tarski(u1_struct_0(B_33),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_33,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_448])).

tff(c_524,plain,(
    ! [B_763] :
      ( ~ m1_connsp_2(u1_struct_0(B_763),'#skF_5','#skF_8')
      | ~ r1_tarski(u1_struct_0(B_763),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_763,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_456])).

tff(c_528,plain,(
    ! [B_680] :
      ( ~ m1_connsp_2(u1_struct_0(B_680),'#skF_5','#skF_8')
      | ~ m1_pre_topc(B_680,'#skF_5')
      | ~ m1_pre_topc(B_680,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_155,c_524])).

tff(c_532,plain,(
    ! [B_764] :
      ( ~ m1_connsp_2(u1_struct_0(B_764),'#skF_5','#skF_8')
      | ~ m1_pre_topc(B_764,'#skF_5')
      | ~ m1_pre_topc(B_764,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_528])).

tff(c_537,plain,(
    ! [B_765] :
      ( ~ m1_pre_topc(B_765,'#skF_4')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_765))
      | ~ m1_pre_topc(B_765,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_350,c_532])).

tff(c_543,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_537])).

tff(c_547,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_543])).

tff(c_550,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_547])).

tff(c_554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_550])).

tff(c_555,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_663,plain,(
    ! [A_809,D_812,E_810,B_811,G_813,C_808] :
      ( r1_tmap_1(D_812,B_811,k3_tmap_1(A_809,B_811,C_808,D_812,E_810),G_813)
      | ~ r1_tmap_1(C_808,B_811,E_810,G_813)
      | ~ m1_pre_topc(D_812,C_808)
      | ~ m1_subset_1(G_813,u1_struct_0(D_812))
      | ~ m1_subset_1(G_813,u1_struct_0(C_808))
      | ~ m1_subset_1(E_810,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_808),u1_struct_0(B_811))))
      | ~ v1_funct_2(E_810,u1_struct_0(C_808),u1_struct_0(B_811))
      | ~ v1_funct_1(E_810)
      | ~ m1_pre_topc(D_812,A_809)
      | v2_struct_0(D_812)
      | ~ m1_pre_topc(C_808,A_809)
      | v2_struct_0(C_808)
      | ~ l1_pre_topc(B_811)
      | ~ v2_pre_topc(B_811)
      | v2_struct_0(B_811)
      | ~ l1_pre_topc(A_809)
      | ~ v2_pre_topc(A_809)
      | v2_struct_0(A_809) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_665,plain,(
    ! [D_812,A_809,G_813] :
      ( r1_tmap_1(D_812,'#skF_3',k3_tmap_1(A_809,'#skF_3','#skF_5',D_812,'#skF_6'),G_813)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_813)
      | ~ m1_pre_topc(D_812,'#skF_5')
      | ~ m1_subset_1(G_813,u1_struct_0(D_812))
      | ~ m1_subset_1(G_813,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_812,A_809)
      | v2_struct_0(D_812)
      | ~ m1_pre_topc('#skF_5',A_809)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_809)
      | ~ v2_pre_topc(A_809)
      | v2_struct_0(A_809) ) ),
    inference(resolution,[status(thm)],[c_48,c_663])).

tff(c_671,plain,(
    ! [D_812,A_809,G_813] :
      ( r1_tmap_1(D_812,'#skF_3',k3_tmap_1(A_809,'#skF_3','#skF_5',D_812,'#skF_6'),G_813)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_813)
      | ~ m1_pre_topc(D_812,'#skF_5')
      | ~ m1_subset_1(G_813,u1_struct_0(D_812))
      | ~ m1_subset_1(G_813,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_812,A_809)
      | v2_struct_0(D_812)
      | ~ m1_pre_topc('#skF_5',A_809)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_809)
      | ~ v2_pre_topc(A_809)
      | v2_struct_0(A_809) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_50,c_665])).

tff(c_788,plain,(
    ! [D_835,A_836,G_837] :
      ( r1_tmap_1(D_835,'#skF_3',k3_tmap_1(A_836,'#skF_3','#skF_5',D_835,'#skF_6'),G_837)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_837)
      | ~ m1_pre_topc(D_835,'#skF_5')
      | ~ m1_subset_1(G_837,u1_struct_0(D_835))
      | ~ m1_subset_1(G_837,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_835,A_836)
      | v2_struct_0(D_835)
      | ~ m1_pre_topc('#skF_5',A_836)
      | ~ l1_pre_topc(A_836)
      | ~ v2_pre_topc(A_836)
      | v2_struct_0(A_836) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_56,c_671])).

tff(c_556,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_793,plain,
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
    inference(resolution,[status(thm)],[c_788,c_556])).

tff(c_800,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_42,c_83,c_46,c_555,c_793])).

tff(c_802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60,c_800])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.65  
% 4.13/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.65  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 4.13/1.65  
% 4.13/1.65  %Foreground sorts:
% 4.13/1.65  
% 4.13/1.65  
% 4.13/1.65  %Background operators:
% 4.13/1.65  
% 4.13/1.65  
% 4.13/1.65  %Foreground operators:
% 4.13/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.13/1.65  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.13/1.65  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.13/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.13/1.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.13/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.65  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.13/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.13/1.65  tff('#skF_7', type, '#skF_7': $i).
% 4.13/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.65  tff('#skF_5', type, '#skF_5': $i).
% 4.13/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.13/1.65  tff('#skF_6', type, '#skF_6': $i).
% 4.13/1.65  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.65  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.65  tff('#skF_9', type, '#skF_9': $i).
% 4.13/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.65  tff('#skF_8', type, '#skF_8': $i).
% 4.13/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.13/1.65  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.13/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.13/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.13/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.65  
% 4.13/1.67  tff(f_253, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.13/1.67  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.13/1.67  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.13/1.67  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.13/1.67  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.13/1.67  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 4.13/1.67  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.13/1.67  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.13/1.67  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.13/1.67  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_32, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_40, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_83, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 4.13/1.67  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_99, plain, (![B_676, A_677]: (l1_pre_topc(B_676) | ~m1_pre_topc(B_676, A_677) | ~l1_pre_topc(A_677))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.13/1.67  tff(c_108, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_99])).
% 4.13/1.67  tff(c_116, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_108])).
% 4.13/1.67  tff(c_22, plain, (![A_34]: (m1_pre_topc(A_34, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.13/1.67  tff(c_34, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_111, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_99])).
% 4.13/1.67  tff(c_119, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_111])).
% 4.13/1.67  tff(c_20, plain, (![B_33, A_31]: (m1_subset_1(u1_struct_0(B_33), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.13/1.67  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_126, plain, (![B_678, A_679]: (v2_pre_topc(B_678) | ~m1_pre_topc(B_678, A_679) | ~l1_pre_topc(A_679) | ~v2_pre_topc(A_679))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.13/1.67  tff(c_138, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_126])).
% 4.13/1.67  tff(c_148, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_138])).
% 4.13/1.67  tff(c_38, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_36, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_303, plain, (![C_725, A_726, B_727, D_728]: (m1_connsp_2(C_725, A_726, B_727) | ~r2_hidden(B_727, D_728) | ~r1_tarski(D_728, C_725) | ~v3_pre_topc(D_728, A_726) | ~m1_subset_1(D_728, k1_zfmisc_1(u1_struct_0(A_726))) | ~m1_subset_1(C_725, k1_zfmisc_1(u1_struct_0(A_726))) | ~m1_subset_1(B_727, u1_struct_0(A_726)) | ~l1_pre_topc(A_726) | ~v2_pre_topc(A_726) | v2_struct_0(A_726))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.13/1.67  tff(c_317, plain, (![C_732, A_733]: (m1_connsp_2(C_732, A_733, '#skF_8') | ~r1_tarski('#skF_7', C_732) | ~v3_pre_topc('#skF_7', A_733) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_733))) | ~m1_subset_1(C_732, k1_zfmisc_1(u1_struct_0(A_733))) | ~m1_subset_1('#skF_8', u1_struct_0(A_733)) | ~l1_pre_topc(A_733) | ~v2_pre_topc(A_733) | v2_struct_0(A_733))), inference(resolution, [status(thm)], [c_36, c_303])).
% 4.13/1.67  tff(c_322, plain, (![C_732]: (m1_connsp_2(C_732, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_732) | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(C_732, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_317])).
% 4.13/1.67  tff(c_326, plain, (![C_732]: (m1_connsp_2(C_732, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_732) | ~m1_subset_1(C_732, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_119, c_42, c_38, c_322])).
% 4.13/1.67  tff(c_328, plain, (![C_734]: (m1_connsp_2(C_734, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_734) | ~m1_subset_1(C_734, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_326])).
% 4.13/1.67  tff(c_336, plain, (![B_33]: (m1_connsp_2(u1_struct_0(B_33), '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(B_33)) | ~m1_pre_topc(B_33, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_328])).
% 4.13/1.67  tff(c_350, plain, (![B_33]: (m1_connsp_2(u1_struct_0(B_33), '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(B_33)) | ~m1_pre_topc(B_33, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_336])).
% 4.13/1.67  tff(c_151, plain, (![B_680, A_681]: (m1_subset_1(u1_struct_0(B_680), k1_zfmisc_1(u1_struct_0(A_681))) | ~m1_pre_topc(B_680, A_681) | ~l1_pre_topc(A_681))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.13/1.67  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.13/1.67  tff(c_155, plain, (![B_680, A_681]: (r1_tarski(u1_struct_0(B_680), u1_struct_0(A_681)) | ~m1_pre_topc(B_680, A_681) | ~l1_pre_topc(A_681))), inference(resolution, [status(thm)], [c_151, c_2])).
% 4.13/1.67  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_80, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_81, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_80])).
% 4.13/1.67  tff(c_210, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_81])).
% 4.13/1.67  tff(c_74, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_82, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_74])).
% 4.13/1.67  tff(c_212, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_82])).
% 4.13/1.67  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_50, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.13/1.67  tff(c_441, plain, (![H_756, C_757, E_758, D_755, F_754, A_752, B_753]: (r1_tmap_1(D_755, B_753, E_758, H_756) | ~r1_tmap_1(C_757, B_753, k3_tmap_1(A_752, B_753, D_755, C_757, E_758), H_756) | ~m1_connsp_2(F_754, D_755, H_756) | ~r1_tarski(F_754, u1_struct_0(C_757)) | ~m1_subset_1(H_756, u1_struct_0(C_757)) | ~m1_subset_1(H_756, u1_struct_0(D_755)) | ~m1_subset_1(F_754, k1_zfmisc_1(u1_struct_0(D_755))) | ~m1_pre_topc(C_757, D_755) | ~m1_subset_1(E_758, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_755), u1_struct_0(B_753)))) | ~v1_funct_2(E_758, u1_struct_0(D_755), u1_struct_0(B_753)) | ~v1_funct_1(E_758) | ~m1_pre_topc(D_755, A_752) | v2_struct_0(D_755) | ~m1_pre_topc(C_757, A_752) | v2_struct_0(C_757) | ~l1_pre_topc(B_753) | ~v2_pre_topc(B_753) | v2_struct_0(B_753) | ~l1_pre_topc(A_752) | ~v2_pre_topc(A_752) | v2_struct_0(A_752))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.13/1.67  tff(c_443, plain, (![F_754]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_754, '#skF_5', '#skF_8') | ~r1_tarski(F_754, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_754, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_210, c_441])).
% 4.13/1.67  tff(c_446, plain, (![F_754]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_754, '#skF_5', '#skF_8') | ~r1_tarski(F_754, u1_struct_0('#skF_4')) | ~m1_subset_1(F_754, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_50, c_48, c_46, c_42, c_83, c_443])).
% 4.13/1.67  tff(c_448, plain, (![F_759]: (~m1_connsp_2(F_759, '#skF_5', '#skF_8') | ~r1_tarski(F_759, u1_struct_0('#skF_4')) | ~m1_subset_1(F_759, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_212, c_446])).
% 4.13/1.67  tff(c_456, plain, (![B_33]: (~m1_connsp_2(u1_struct_0(B_33), '#skF_5', '#skF_8') | ~r1_tarski(u1_struct_0(B_33), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_33, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_448])).
% 4.13/1.67  tff(c_524, plain, (![B_763]: (~m1_connsp_2(u1_struct_0(B_763), '#skF_5', '#skF_8') | ~r1_tarski(u1_struct_0(B_763), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_763, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_456])).
% 4.13/1.67  tff(c_528, plain, (![B_680]: (~m1_connsp_2(u1_struct_0(B_680), '#skF_5', '#skF_8') | ~m1_pre_topc(B_680, '#skF_5') | ~m1_pre_topc(B_680, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_155, c_524])).
% 4.13/1.67  tff(c_532, plain, (![B_764]: (~m1_connsp_2(u1_struct_0(B_764), '#skF_5', '#skF_8') | ~m1_pre_topc(B_764, '#skF_5') | ~m1_pre_topc(B_764, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_528])).
% 4.13/1.67  tff(c_537, plain, (![B_765]: (~m1_pre_topc(B_765, '#skF_4') | ~r1_tarski('#skF_7', u1_struct_0(B_765)) | ~m1_pre_topc(B_765, '#skF_5'))), inference(resolution, [status(thm)], [c_350, c_532])).
% 4.13/1.67  tff(c_543, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_537])).
% 4.13/1.67  tff(c_547, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_543])).
% 4.13/1.67  tff(c_550, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_547])).
% 4.13/1.67  tff(c_554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_550])).
% 4.13/1.67  tff(c_555, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 4.13/1.67  tff(c_663, plain, (![A_809, D_812, E_810, B_811, G_813, C_808]: (r1_tmap_1(D_812, B_811, k3_tmap_1(A_809, B_811, C_808, D_812, E_810), G_813) | ~r1_tmap_1(C_808, B_811, E_810, G_813) | ~m1_pre_topc(D_812, C_808) | ~m1_subset_1(G_813, u1_struct_0(D_812)) | ~m1_subset_1(G_813, u1_struct_0(C_808)) | ~m1_subset_1(E_810, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_808), u1_struct_0(B_811)))) | ~v1_funct_2(E_810, u1_struct_0(C_808), u1_struct_0(B_811)) | ~v1_funct_1(E_810) | ~m1_pre_topc(D_812, A_809) | v2_struct_0(D_812) | ~m1_pre_topc(C_808, A_809) | v2_struct_0(C_808) | ~l1_pre_topc(B_811) | ~v2_pre_topc(B_811) | v2_struct_0(B_811) | ~l1_pre_topc(A_809) | ~v2_pre_topc(A_809) | v2_struct_0(A_809))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.13/1.67  tff(c_665, plain, (![D_812, A_809, G_813]: (r1_tmap_1(D_812, '#skF_3', k3_tmap_1(A_809, '#skF_3', '#skF_5', D_812, '#skF_6'), G_813) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_813) | ~m1_pre_topc(D_812, '#skF_5') | ~m1_subset_1(G_813, u1_struct_0(D_812)) | ~m1_subset_1(G_813, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_812, A_809) | v2_struct_0(D_812) | ~m1_pre_topc('#skF_5', A_809) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_809) | ~v2_pre_topc(A_809) | v2_struct_0(A_809))), inference(resolution, [status(thm)], [c_48, c_663])).
% 4.13/1.67  tff(c_671, plain, (![D_812, A_809, G_813]: (r1_tmap_1(D_812, '#skF_3', k3_tmap_1(A_809, '#skF_3', '#skF_5', D_812, '#skF_6'), G_813) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_813) | ~m1_pre_topc(D_812, '#skF_5') | ~m1_subset_1(G_813, u1_struct_0(D_812)) | ~m1_subset_1(G_813, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_812, A_809) | v2_struct_0(D_812) | ~m1_pre_topc('#skF_5', A_809) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_809) | ~v2_pre_topc(A_809) | v2_struct_0(A_809))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_50, c_665])).
% 4.13/1.67  tff(c_788, plain, (![D_835, A_836, G_837]: (r1_tmap_1(D_835, '#skF_3', k3_tmap_1(A_836, '#skF_3', '#skF_5', D_835, '#skF_6'), G_837) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_837) | ~m1_pre_topc(D_835, '#skF_5') | ~m1_subset_1(G_837, u1_struct_0(D_835)) | ~m1_subset_1(G_837, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_835, A_836) | v2_struct_0(D_835) | ~m1_pre_topc('#skF_5', A_836) | ~l1_pre_topc(A_836) | ~v2_pre_topc(A_836) | v2_struct_0(A_836))), inference(negUnitSimplification, [status(thm)], [c_66, c_56, c_671])).
% 4.13/1.67  tff(c_556, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 4.13/1.67  tff(c_793, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_788, c_556])).
% 4.13/1.67  tff(c_800, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_42, c_83, c_46, c_555, c_793])).
% 4.13/1.67  tff(c_802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_60, c_800])).
% 4.13/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.67  
% 4.13/1.67  Inference rules
% 4.13/1.67  ----------------------
% 4.13/1.67  #Ref     : 0
% 4.13/1.67  #Sup     : 130
% 4.13/1.67  #Fact    : 0
% 4.13/1.67  #Define  : 0
% 4.13/1.67  #Split   : 5
% 4.13/1.67  #Chain   : 0
% 4.13/1.67  #Close   : 0
% 4.13/1.67  
% 4.13/1.67  Ordering : KBO
% 4.13/1.67  
% 4.13/1.67  Simplification rules
% 4.13/1.67  ----------------------
% 4.13/1.67  #Subsume      : 16
% 4.13/1.67  #Demod        : 156
% 4.13/1.67  #Tautology    : 20
% 4.13/1.67  #SimpNegUnit  : 25
% 4.13/1.67  #BackRed      : 0
% 4.13/1.67  
% 4.13/1.67  #Partial instantiations: 0
% 4.13/1.67  #Strategies tried      : 1
% 4.13/1.67  
% 4.13/1.67  Timing (in seconds)
% 4.13/1.67  ----------------------
% 4.13/1.68  Preprocessing        : 0.43
% 4.13/1.68  Parsing              : 0.21
% 4.13/1.68  CNF conversion       : 0.08
% 4.13/1.68  Main loop            : 0.48
% 4.13/1.68  Inferencing          : 0.18
% 4.13/1.68  Reduction            : 0.15
% 4.13/1.68  Demodulation         : 0.11
% 4.13/1.68  BG Simplification    : 0.03
% 4.13/1.68  Subsumption          : 0.09
% 4.13/1.68  Abstraction          : 0.02
% 4.13/1.68  MUC search           : 0.00
% 4.13/1.68  Cooper               : 0.00
% 4.13/1.68  Total                : 0.96
% 4.13/1.68  Index Insertion      : 0.00
% 4.13/1.68  Index Deletion       : 0.00
% 4.13/1.68  Index Matching       : 0.00
% 4.13/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
