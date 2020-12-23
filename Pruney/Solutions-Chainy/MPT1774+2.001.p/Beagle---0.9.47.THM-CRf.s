%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:24 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 486 expanded)
%              Number of leaves         :   41 ( 192 expanded)
%              Depth                    :   13
%              Number of atoms          :  431 (3360 expanded)
%              Number of equality atoms :    6 ( 121 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_289,negated_conjecture,(
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
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,B)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,A,E,G)
                                        <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_231,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_116,axiom,(
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

tff(f_176,axiom,(
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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_62,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_40,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_48,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_91,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_42,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_98,plain,(
    ! [B_689,A_690] :
      ( l1_pre_topc(B_689)
      | ~ m1_pre_topc(B_689,A_690)
      | ~ l1_pre_topc(A_690) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_104,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_98])).

tff(c_111,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_104])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_264,plain,(
    ! [C_717,A_718,B_719] :
      ( m1_subset_1(C_717,k1_zfmisc_1(u1_struct_0(A_718)))
      | ~ m1_subset_1(C_717,k1_zfmisc_1(u1_struct_0(B_719)))
      | ~ m1_pre_topc(B_719,A_718)
      | ~ l1_pre_topc(A_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_323,plain,(
    ! [A_732,A_733,B_734] :
      ( m1_subset_1(A_732,k1_zfmisc_1(u1_struct_0(A_733)))
      | ~ m1_pre_topc(B_734,A_733)
      | ~ l1_pre_topc(A_733)
      | ~ r1_tarski(A_732,u1_struct_0(B_734)) ) ),
    inference(resolution,[status(thm)],[c_16,c_264])).

tff(c_327,plain,(
    ! [A_732] :
      ( m1_subset_1(A_732,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_732,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_323])).

tff(c_335,plain,(
    ! [A_732] :
      ( m1_subset_1(A_732,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_732,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_327])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_90,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_176,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_58,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_89,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_88])).

tff(c_289,plain,(
    r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_89])).

tff(c_1046,plain,(
    ! [C_785,D_789,B_788,A_790,H_786,F_784,E_787] :
      ( r1_tmap_1(D_789,B_788,E_787,H_786)
      | ~ r1_tmap_1(C_785,B_788,k3_tmap_1(A_790,B_788,D_789,C_785,E_787),H_786)
      | ~ m1_connsp_2(F_784,D_789,H_786)
      | ~ r1_tarski(F_784,u1_struct_0(C_785))
      | ~ m1_subset_1(H_786,u1_struct_0(C_785))
      | ~ m1_subset_1(H_786,u1_struct_0(D_789))
      | ~ m1_subset_1(F_784,k1_zfmisc_1(u1_struct_0(D_789)))
      | ~ m1_pre_topc(C_785,D_789)
      | ~ m1_subset_1(E_787,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_789),u1_struct_0(B_788))))
      | ~ v1_funct_2(E_787,u1_struct_0(D_789),u1_struct_0(B_788))
      | ~ v1_funct_1(E_787)
      | ~ m1_pre_topc(D_789,A_790)
      | v2_struct_0(D_789)
      | ~ m1_pre_topc(C_785,A_790)
      | v2_struct_0(C_785)
      | ~ l1_pre_topc(B_788)
      | ~ v2_pre_topc(B_788)
      | v2_struct_0(B_788)
      | ~ l1_pre_topc(A_790)
      | ~ v2_pre_topc(A_790)
      | v2_struct_0(A_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_1048,plain,(
    ! [F_784] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_784,'#skF_5','#skF_8')
      | ~ r1_tarski(F_784,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_784,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_289,c_1046])).

tff(c_1051,plain,(
    ! [F_784] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_784,'#skF_5','#skF_8')
      | ~ r1_tarski(F_784,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_784,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_78,c_76,c_66,c_62,c_60,c_58,c_56,c_54,c_50,c_91,c_1048])).

tff(c_1053,plain,(
    ! [F_791] :
      ( ~ m1_connsp_2(F_791,'#skF_5','#skF_8')
      | ~ r1_tarski(F_791,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_791,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_80,c_68,c_64,c_176,c_1051])).

tff(c_1086,plain,(
    ! [A_794] :
      ( ~ m1_connsp_2(A_794,'#skF_5','#skF_8')
      | ~ r1_tarski(A_794,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_335,c_1053])).

tff(c_1105,plain,(
    ~ m1_connsp_2('#skF_7','#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_1086])).

tff(c_342,plain,(
    ! [A_735] :
      ( m1_subset_1(A_735,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_735,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_327])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_352,plain,(
    ! [A_735] :
      ( r1_tarski(A_735,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_735,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_342,c_14])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_329,plain,(
    ! [A_732] :
      ( m1_subset_1(A_732,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_732,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_62,c_323])).

tff(c_353,plain,(
    ! [A_736] :
      ( m1_subset_1(A_736,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_736,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_329])).

tff(c_404,plain,(
    ! [A_739] :
      ( r1_tarski(A_739,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_739,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_353,c_14])).

tff(c_420,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_404])).

tff(c_46,plain,(
    v3_pre_topc('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_439,plain,(
    ! [B_740,A_741,C_742] :
      ( r1_tarski(B_740,k1_tops_1(A_741,C_742))
      | ~ r1_tarski(B_740,C_742)
      | ~ v3_pre_topc(B_740,A_741)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(u1_struct_0(A_741)))
      | ~ m1_subset_1(B_740,k1_zfmisc_1(u1_struct_0(A_741)))
      | ~ l1_pre_topc(A_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1405,plain,(
    ! [B_814,A_815,A_816] :
      ( r1_tarski(B_814,k1_tops_1(A_815,A_816))
      | ~ r1_tarski(B_814,A_816)
      | ~ v3_pre_topc(B_814,A_815)
      | ~ m1_subset_1(B_814,k1_zfmisc_1(u1_struct_0(A_815)))
      | ~ l1_pre_topc(A_815)
      | ~ r1_tarski(A_816,u1_struct_0(A_815)) ) ),
    inference(resolution,[status(thm)],[c_16,c_439])).

tff(c_1422,plain,(
    ! [A_816] :
      ( r1_tarski('#skF_7',k1_tops_1('#skF_3',A_816))
      | ~ r1_tarski('#skF_7',A_816)
      | ~ v3_pre_topc('#skF_7','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_816,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_52,c_1405])).

tff(c_1439,plain,(
    ! [A_817] :
      ( r1_tarski('#skF_7',k1_tops_1('#skF_3',A_817))
      | ~ r1_tarski('#skF_7',A_817)
      | ~ r1_tarski(A_817,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_46,c_1422])).

tff(c_1474,plain,
    ( r1_tarski('#skF_7',k1_tops_1('#skF_3',u1_struct_0('#skF_5')))
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_420,c_1439])).

tff(c_1548,plain,(
    ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1474])).

tff(c_1554,plain,(
    ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_352,c_1548])).

tff(c_1564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1554])).

tff(c_1566,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1474])).

tff(c_311,plain,(
    ! [D_729,C_730,A_731] :
      ( v3_pre_topc(D_729,C_730)
      | ~ m1_subset_1(D_729,k1_zfmisc_1(u1_struct_0(C_730)))
      | ~ v3_pre_topc(D_729,A_731)
      | ~ m1_pre_topc(C_730,A_731)
      | ~ m1_subset_1(D_729,k1_zfmisc_1(u1_struct_0(A_731)))
      | ~ l1_pre_topc(A_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1108,plain,(
    ! [A_796,C_797,A_798] :
      ( v3_pre_topc(A_796,C_797)
      | ~ v3_pre_topc(A_796,A_798)
      | ~ m1_pre_topc(C_797,A_798)
      | ~ m1_subset_1(A_796,k1_zfmisc_1(u1_struct_0(A_798)))
      | ~ l1_pre_topc(A_798)
      | ~ r1_tarski(A_796,u1_struct_0(C_797)) ) ),
    inference(resolution,[status(thm)],[c_16,c_311])).

tff(c_1112,plain,(
    ! [A_796] :
      ( v3_pre_topc(A_796,'#skF_4')
      | ~ v3_pre_topc(A_796,'#skF_5')
      | ~ m1_subset_1(A_796,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_796,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_1108])).

tff(c_1731,plain,(
    ! [A_834] :
      ( v3_pre_topc(A_834,'#skF_4')
      | ~ v3_pre_topc(A_834,'#skF_5')
      | ~ m1_subset_1(A_834,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_834,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1112])).

tff(c_1824,plain,(
    ! [A_836] :
      ( v3_pre_topc(A_836,'#skF_4')
      | ~ v3_pre_topc(A_836,'#skF_5')
      | ~ r1_tarski(A_836,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_335,c_1731])).

tff(c_1864,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1824])).

tff(c_1866,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1864])).

tff(c_1114,plain,(
    ! [A_796] :
      ( v3_pre_topc(A_796,'#skF_5')
      | ~ v3_pre_topc(A_796,'#skF_3')
      | ~ m1_subset_1(A_796,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_796,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_62,c_1108])).

tff(c_1879,plain,(
    ! [A_843] :
      ( v3_pre_topc(A_843,'#skF_5')
      | ~ v3_pre_topc(A_843,'#skF_3')
      | ~ m1_subset_1(A_843,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_843,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1114])).

tff(c_1904,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_3')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_1879])).

tff(c_1920,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1566,c_46,c_1904])).

tff(c_1922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1866,c_1920])).

tff(c_1924,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1864])).

tff(c_3655,plain,(
    ! [A_913,A_914,A_915] :
      ( r1_tarski(A_913,k1_tops_1(A_914,A_915))
      | ~ r1_tarski(A_913,A_915)
      | ~ v3_pre_topc(A_913,A_914)
      | ~ l1_pre_topc(A_914)
      | ~ r1_tarski(A_915,u1_struct_0(A_914))
      | ~ r1_tarski(A_913,u1_struct_0(A_914)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1405])).

tff(c_3667,plain,(
    ! [A_913] :
      ( r1_tarski(A_913,k1_tops_1('#skF_5','#skF_7'))
      | ~ r1_tarski(A_913,'#skF_7')
      | ~ v3_pre_topc(A_913,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_913,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1566,c_3655])).

tff(c_5946,plain,(
    ! [A_978] :
      ( r1_tarski(A_978,k1_tops_1('#skF_5','#skF_7'))
      | ~ r1_tarski(A_978,'#skF_7')
      | ~ v3_pre_topc(A_978,'#skF_5')
      | ~ r1_tarski(A_978,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_3667])).

tff(c_157,plain,(
    ! [B_701,A_702] :
      ( v2_pre_topc(B_701)
      | ~ m1_pre_topc(B_701,A_702)
      | ~ l1_pre_topc(A_702)
      | ~ v2_pre_topc(A_702) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_163,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_157])).

tff(c_172,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_163])).

tff(c_44,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_179,plain,(
    ! [C_703,B_704,A_705] :
      ( r2_hidden(C_703,B_704)
      | ~ r2_hidden(C_703,A_705)
      | ~ r1_tarski(A_705,B_704) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [B_704] :
      ( r2_hidden('#skF_8',B_704)
      | ~ r1_tarski('#skF_7',B_704) ) ),
    inference(resolution,[status(thm)],[c_44,c_179])).

tff(c_539,plain,(
    ! [C_747,A_748,B_749] :
      ( m1_connsp_2(C_747,A_748,B_749)
      | ~ r2_hidden(B_749,k1_tops_1(A_748,C_747))
      | ~ m1_subset_1(C_747,k1_zfmisc_1(u1_struct_0(A_748)))
      | ~ m1_subset_1(B_749,u1_struct_0(A_748))
      | ~ l1_pre_topc(A_748)
      | ~ v2_pre_topc(A_748)
      | v2_struct_0(A_748) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5076,plain,(
    ! [C_954,A_955] :
      ( m1_connsp_2(C_954,A_955,'#skF_8')
      | ~ m1_subset_1(C_954,k1_zfmisc_1(u1_struct_0(A_955)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_955))
      | ~ l1_pre_topc(A_955)
      | ~ v2_pre_topc(A_955)
      | v2_struct_0(A_955)
      | ~ r1_tarski('#skF_7',k1_tops_1(A_955,C_954)) ) ),
    inference(resolution,[status(thm)],[c_185,c_539])).

tff(c_5112,plain,(
    ! [A_732] :
      ( m1_connsp_2(A_732,'#skF_5','#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski('#skF_7',k1_tops_1('#skF_5',A_732))
      | ~ r1_tarski(A_732,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_335,c_5076])).

tff(c_5151,plain,(
    ! [A_732] :
      ( m1_connsp_2(A_732,'#skF_5','#skF_8')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski('#skF_7',k1_tops_1('#skF_5',A_732))
      | ~ r1_tarski(A_732,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_111,c_50,c_5112])).

tff(c_5152,plain,(
    ! [A_732] :
      ( m1_connsp_2(A_732,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',k1_tops_1('#skF_5',A_732))
      | ~ r1_tarski(A_732,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5151])).

tff(c_5963,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_7','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5946,c_5152])).

tff(c_6063,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1566,c_1924,c_12,c_42,c_5963])).

tff(c_6065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1105,c_6063])).

tff(c_6067,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_6843,plain,(
    ! [E_1058,G_1059,C_1056,D_1057,B_1060,A_1055] :
      ( r1_tmap_1(D_1057,B_1060,k3_tmap_1(A_1055,B_1060,C_1056,D_1057,E_1058),G_1059)
      | ~ r1_tmap_1(C_1056,B_1060,E_1058,G_1059)
      | ~ m1_pre_topc(D_1057,C_1056)
      | ~ m1_subset_1(G_1059,u1_struct_0(D_1057))
      | ~ m1_subset_1(G_1059,u1_struct_0(C_1056))
      | ~ m1_subset_1(E_1058,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1056),u1_struct_0(B_1060))))
      | ~ v1_funct_2(E_1058,u1_struct_0(C_1056),u1_struct_0(B_1060))
      | ~ v1_funct_1(E_1058)
      | ~ m1_pre_topc(D_1057,A_1055)
      | v2_struct_0(D_1057)
      | ~ m1_pre_topc(C_1056,A_1055)
      | v2_struct_0(C_1056)
      | ~ l1_pre_topc(B_1060)
      | ~ v2_pre_topc(B_1060)
      | v2_struct_0(B_1060)
      | ~ l1_pre_topc(A_1055)
      | ~ v2_pre_topc(A_1055)
      | v2_struct_0(A_1055) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_6845,plain,(
    ! [D_1057,A_1055,G_1059] :
      ( r1_tmap_1(D_1057,'#skF_2',k3_tmap_1(A_1055,'#skF_2','#skF_5',D_1057,'#skF_6'),G_1059)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_1059)
      | ~ m1_pre_topc(D_1057,'#skF_5')
      | ~ m1_subset_1(G_1059,u1_struct_0(D_1057))
      | ~ m1_subset_1(G_1059,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_1057,A_1055)
      | v2_struct_0(D_1057)
      | ~ m1_pre_topc('#skF_5',A_1055)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1055)
      | ~ v2_pre_topc(A_1055)
      | v2_struct_0(A_1055) ) ),
    inference(resolution,[status(thm)],[c_56,c_6843])).

tff(c_6851,plain,(
    ! [D_1057,A_1055,G_1059] :
      ( r1_tmap_1(D_1057,'#skF_2',k3_tmap_1(A_1055,'#skF_2','#skF_5',D_1057,'#skF_6'),G_1059)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_1059)
      | ~ m1_pre_topc(D_1057,'#skF_5')
      | ~ m1_subset_1(G_1059,u1_struct_0(D_1057))
      | ~ m1_subset_1(G_1059,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1057,A_1055)
      | v2_struct_0(D_1057)
      | ~ m1_pre_topc('#skF_5',A_1055)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1055)
      | ~ v2_pre_topc(A_1055)
      | v2_struct_0(A_1055) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_60,c_58,c_6845])).

tff(c_7904,plain,(
    ! [D_1112,A_1113,G_1114] :
      ( r1_tmap_1(D_1112,'#skF_2',k3_tmap_1(A_1113,'#skF_2','#skF_5',D_1112,'#skF_6'),G_1114)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_1114)
      | ~ m1_pre_topc(D_1112,'#skF_5')
      | ~ m1_subset_1(G_1114,u1_struct_0(D_1112))
      | ~ m1_subset_1(G_1114,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1112,A_1113)
      | v2_struct_0(D_1112)
      | ~ m1_pre_topc('#skF_5',A_1113)
      | ~ l1_pre_topc(A_1113)
      | ~ v2_pre_topc(A_1113)
      | v2_struct_0(A_1113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_64,c_6851])).

tff(c_6066,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_7909,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7904,c_6066])).

tff(c_7916,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_62,c_66,c_50,c_91,c_54,c_6067,c_7909])).

tff(c_7918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_7916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:15:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.98/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.98/2.61  
% 7.98/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.98/2.61  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 7.98/2.61  
% 7.98/2.61  %Foreground sorts:
% 7.98/2.61  
% 7.98/2.61  
% 7.98/2.61  %Background operators:
% 7.98/2.61  
% 7.98/2.61  
% 7.98/2.61  %Foreground operators:
% 7.98/2.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.98/2.61  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.98/2.61  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.98/2.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.98/2.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.98/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.98/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.98/2.61  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.98/2.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.98/2.61  tff('#skF_7', type, '#skF_7': $i).
% 7.98/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.98/2.61  tff('#skF_5', type, '#skF_5': $i).
% 7.98/2.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.98/2.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.98/2.61  tff('#skF_6', type, '#skF_6': $i).
% 7.98/2.61  tff('#skF_2', type, '#skF_2': $i).
% 7.98/2.61  tff('#skF_3', type, '#skF_3': $i).
% 7.98/2.61  tff('#skF_9', type, '#skF_9': $i).
% 7.98/2.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.98/2.61  tff('#skF_8', type, '#skF_8': $i).
% 7.98/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.98/2.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.98/2.61  tff('#skF_4', type, '#skF_4': $i).
% 7.98/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.98/2.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.98/2.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.98/2.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.98/2.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.98/2.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.98/2.61  
% 7.98/2.64  tff(f_289, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 7.98/2.64  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.98/2.64  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.98/2.64  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 7.98/2.64  tff(f_231, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 7.98/2.64  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.98/2.64  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 7.98/2.64  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 7.98/2.64  tff(f_51, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.98/2.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.98/2.64  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 7.98/2.64  tff(f_176, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 7.98/2.64  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_62, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_50, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_40, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_48, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_91, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48])).
% 7.98/2.64  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_42, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_98, plain, (![B_689, A_690]: (l1_pre_topc(B_689) | ~m1_pre_topc(B_689, A_690) | ~l1_pre_topc(A_690))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.98/2.64  tff(c_104, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_98])).
% 7.98/2.64  tff(c_111, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_104])).
% 7.98/2.64  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.98/2.64  tff(c_264, plain, (![C_717, A_718, B_719]: (m1_subset_1(C_717, k1_zfmisc_1(u1_struct_0(A_718))) | ~m1_subset_1(C_717, k1_zfmisc_1(u1_struct_0(B_719))) | ~m1_pre_topc(B_719, A_718) | ~l1_pre_topc(A_718))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.98/2.64  tff(c_323, plain, (![A_732, A_733, B_734]: (m1_subset_1(A_732, k1_zfmisc_1(u1_struct_0(A_733))) | ~m1_pre_topc(B_734, A_733) | ~l1_pre_topc(A_733) | ~r1_tarski(A_732, u1_struct_0(B_734)))), inference(resolution, [status(thm)], [c_16, c_264])).
% 7.98/2.64  tff(c_327, plain, (![A_732]: (m1_subset_1(A_732, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_732, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_323])).
% 7.98/2.64  tff(c_335, plain, (![A_732]: (m1_subset_1(A_732, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_732, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_327])).
% 7.98/2.64  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_82, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_90, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82])).
% 7.98/2.64  tff(c_176, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 7.98/2.64  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_58, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_88, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_89, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_88])).
% 7.98/2.64  tff(c_289, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_176, c_89])).
% 7.98/2.64  tff(c_1046, plain, (![C_785, D_789, B_788, A_790, H_786, F_784, E_787]: (r1_tmap_1(D_789, B_788, E_787, H_786) | ~r1_tmap_1(C_785, B_788, k3_tmap_1(A_790, B_788, D_789, C_785, E_787), H_786) | ~m1_connsp_2(F_784, D_789, H_786) | ~r1_tarski(F_784, u1_struct_0(C_785)) | ~m1_subset_1(H_786, u1_struct_0(C_785)) | ~m1_subset_1(H_786, u1_struct_0(D_789)) | ~m1_subset_1(F_784, k1_zfmisc_1(u1_struct_0(D_789))) | ~m1_pre_topc(C_785, D_789) | ~m1_subset_1(E_787, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_789), u1_struct_0(B_788)))) | ~v1_funct_2(E_787, u1_struct_0(D_789), u1_struct_0(B_788)) | ~v1_funct_1(E_787) | ~m1_pre_topc(D_789, A_790) | v2_struct_0(D_789) | ~m1_pre_topc(C_785, A_790) | v2_struct_0(C_785) | ~l1_pre_topc(B_788) | ~v2_pre_topc(B_788) | v2_struct_0(B_788) | ~l1_pre_topc(A_790) | ~v2_pre_topc(A_790) | v2_struct_0(A_790))), inference(cnfTransformation, [status(thm)], [f_231])).
% 7.98/2.64  tff(c_1048, plain, (![F_784]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_connsp_2(F_784, '#skF_5', '#skF_8') | ~r1_tarski(F_784, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_784, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_289, c_1046])).
% 7.98/2.64  tff(c_1051, plain, (![F_784]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_connsp_2(F_784, '#skF_5', '#skF_8') | ~r1_tarski(F_784, u1_struct_0('#skF_4')) | ~m1_subset_1(F_784, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_78, c_76, c_66, c_62, c_60, c_58, c_56, c_54, c_50, c_91, c_1048])).
% 7.98/2.64  tff(c_1053, plain, (![F_791]: (~m1_connsp_2(F_791, '#skF_5', '#skF_8') | ~r1_tarski(F_791, u1_struct_0('#skF_4')) | ~m1_subset_1(F_791, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_80, c_68, c_64, c_176, c_1051])).
% 7.98/2.64  tff(c_1086, plain, (![A_794]: (~m1_connsp_2(A_794, '#skF_5', '#skF_8') | ~r1_tarski(A_794, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_335, c_1053])).
% 7.98/2.64  tff(c_1105, plain, (~m1_connsp_2('#skF_7', '#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_42, c_1086])).
% 7.98/2.64  tff(c_342, plain, (![A_735]: (m1_subset_1(A_735, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_735, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_327])).
% 7.98/2.64  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.98/2.64  tff(c_352, plain, (![A_735]: (r1_tarski(A_735, u1_struct_0('#skF_5')) | ~r1_tarski(A_735, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_342, c_14])).
% 7.98/2.64  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.98/2.64  tff(c_329, plain, (![A_732]: (m1_subset_1(A_732, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_732, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_62, c_323])).
% 7.98/2.64  tff(c_353, plain, (![A_736]: (m1_subset_1(A_736, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_736, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_329])).
% 7.98/2.64  tff(c_404, plain, (![A_739]: (r1_tarski(A_739, u1_struct_0('#skF_3')) | ~r1_tarski(A_739, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_353, c_14])).
% 7.98/2.64  tff(c_420, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_404])).
% 7.98/2.64  tff(c_46, plain, (v3_pre_topc('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_439, plain, (![B_740, A_741, C_742]: (r1_tarski(B_740, k1_tops_1(A_741, C_742)) | ~r1_tarski(B_740, C_742) | ~v3_pre_topc(B_740, A_741) | ~m1_subset_1(C_742, k1_zfmisc_1(u1_struct_0(A_741))) | ~m1_subset_1(B_740, k1_zfmisc_1(u1_struct_0(A_741))) | ~l1_pre_topc(A_741))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.98/2.64  tff(c_1405, plain, (![B_814, A_815, A_816]: (r1_tarski(B_814, k1_tops_1(A_815, A_816)) | ~r1_tarski(B_814, A_816) | ~v3_pre_topc(B_814, A_815) | ~m1_subset_1(B_814, k1_zfmisc_1(u1_struct_0(A_815))) | ~l1_pre_topc(A_815) | ~r1_tarski(A_816, u1_struct_0(A_815)))), inference(resolution, [status(thm)], [c_16, c_439])).
% 7.98/2.64  tff(c_1422, plain, (![A_816]: (r1_tarski('#skF_7', k1_tops_1('#skF_3', A_816)) | ~r1_tarski('#skF_7', A_816) | ~v3_pre_topc('#skF_7', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_816, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_52, c_1405])).
% 7.98/2.64  tff(c_1439, plain, (![A_817]: (r1_tarski('#skF_7', k1_tops_1('#skF_3', A_817)) | ~r1_tarski('#skF_7', A_817) | ~r1_tarski(A_817, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_46, c_1422])).
% 7.98/2.64  tff(c_1474, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_3', u1_struct_0('#skF_5'))) | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_420, c_1439])).
% 7.98/2.64  tff(c_1548, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1474])).
% 7.98/2.64  tff(c_1554, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_352, c_1548])).
% 7.98/2.64  tff(c_1564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1554])).
% 7.98/2.64  tff(c_1566, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1474])).
% 7.98/2.64  tff(c_311, plain, (![D_729, C_730, A_731]: (v3_pre_topc(D_729, C_730) | ~m1_subset_1(D_729, k1_zfmisc_1(u1_struct_0(C_730))) | ~v3_pre_topc(D_729, A_731) | ~m1_pre_topc(C_730, A_731) | ~m1_subset_1(D_729, k1_zfmisc_1(u1_struct_0(A_731))) | ~l1_pre_topc(A_731))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.98/2.64  tff(c_1108, plain, (![A_796, C_797, A_798]: (v3_pre_topc(A_796, C_797) | ~v3_pre_topc(A_796, A_798) | ~m1_pre_topc(C_797, A_798) | ~m1_subset_1(A_796, k1_zfmisc_1(u1_struct_0(A_798))) | ~l1_pre_topc(A_798) | ~r1_tarski(A_796, u1_struct_0(C_797)))), inference(resolution, [status(thm)], [c_16, c_311])).
% 7.98/2.64  tff(c_1112, plain, (![A_796]: (v3_pre_topc(A_796, '#skF_4') | ~v3_pre_topc(A_796, '#skF_5') | ~m1_subset_1(A_796, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_796, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_1108])).
% 7.98/2.64  tff(c_1731, plain, (![A_834]: (v3_pre_topc(A_834, '#skF_4') | ~v3_pre_topc(A_834, '#skF_5') | ~m1_subset_1(A_834, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_834, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1112])).
% 7.98/2.64  tff(c_1824, plain, (![A_836]: (v3_pre_topc(A_836, '#skF_4') | ~v3_pre_topc(A_836, '#skF_5') | ~r1_tarski(A_836, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_335, c_1731])).
% 7.98/2.64  tff(c_1864, plain, (v3_pre_topc('#skF_7', '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_1824])).
% 7.98/2.64  tff(c_1866, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_1864])).
% 7.98/2.64  tff(c_1114, plain, (![A_796]: (v3_pre_topc(A_796, '#skF_5') | ~v3_pre_topc(A_796, '#skF_3') | ~m1_subset_1(A_796, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_796, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_62, c_1108])).
% 7.98/2.64  tff(c_1879, plain, (![A_843]: (v3_pre_topc(A_843, '#skF_5') | ~v3_pre_topc(A_843, '#skF_3') | ~m1_subset_1(A_843, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_843, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1114])).
% 7.98/2.64  tff(c_1904, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_3') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_1879])).
% 7.98/2.64  tff(c_1920, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1566, c_46, c_1904])).
% 7.98/2.64  tff(c_1922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1866, c_1920])).
% 7.98/2.64  tff(c_1924, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_1864])).
% 7.98/2.64  tff(c_3655, plain, (![A_913, A_914, A_915]: (r1_tarski(A_913, k1_tops_1(A_914, A_915)) | ~r1_tarski(A_913, A_915) | ~v3_pre_topc(A_913, A_914) | ~l1_pre_topc(A_914) | ~r1_tarski(A_915, u1_struct_0(A_914)) | ~r1_tarski(A_913, u1_struct_0(A_914)))), inference(resolution, [status(thm)], [c_16, c_1405])).
% 7.98/2.64  tff(c_3667, plain, (![A_913]: (r1_tarski(A_913, k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski(A_913, '#skF_7') | ~v3_pre_topc(A_913, '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_913, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1566, c_3655])).
% 7.98/2.64  tff(c_5946, plain, (![A_978]: (r1_tarski(A_978, k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski(A_978, '#skF_7') | ~v3_pre_topc(A_978, '#skF_5') | ~r1_tarski(A_978, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_3667])).
% 7.98/2.64  tff(c_157, plain, (![B_701, A_702]: (v2_pre_topc(B_701) | ~m1_pre_topc(B_701, A_702) | ~l1_pre_topc(A_702) | ~v2_pre_topc(A_702))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.98/2.64  tff(c_163, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_157])).
% 7.98/2.64  tff(c_172, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_163])).
% 7.98/2.64  tff(c_44, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.98/2.64  tff(c_179, plain, (![C_703, B_704, A_705]: (r2_hidden(C_703, B_704) | ~r2_hidden(C_703, A_705) | ~r1_tarski(A_705, B_704))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.98/2.64  tff(c_185, plain, (![B_704]: (r2_hidden('#skF_8', B_704) | ~r1_tarski('#skF_7', B_704))), inference(resolution, [status(thm)], [c_44, c_179])).
% 7.98/2.64  tff(c_539, plain, (![C_747, A_748, B_749]: (m1_connsp_2(C_747, A_748, B_749) | ~r2_hidden(B_749, k1_tops_1(A_748, C_747)) | ~m1_subset_1(C_747, k1_zfmisc_1(u1_struct_0(A_748))) | ~m1_subset_1(B_749, u1_struct_0(A_748)) | ~l1_pre_topc(A_748) | ~v2_pre_topc(A_748) | v2_struct_0(A_748))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.98/2.64  tff(c_5076, plain, (![C_954, A_955]: (m1_connsp_2(C_954, A_955, '#skF_8') | ~m1_subset_1(C_954, k1_zfmisc_1(u1_struct_0(A_955))) | ~m1_subset_1('#skF_8', u1_struct_0(A_955)) | ~l1_pre_topc(A_955) | ~v2_pre_topc(A_955) | v2_struct_0(A_955) | ~r1_tarski('#skF_7', k1_tops_1(A_955, C_954)))), inference(resolution, [status(thm)], [c_185, c_539])).
% 7.98/2.64  tff(c_5112, plain, (![A_732]: (m1_connsp_2(A_732, '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski('#skF_7', k1_tops_1('#skF_5', A_732)) | ~r1_tarski(A_732, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_335, c_5076])).
% 7.98/2.64  tff(c_5151, plain, (![A_732]: (m1_connsp_2(A_732, '#skF_5', '#skF_8') | v2_struct_0('#skF_5') | ~r1_tarski('#skF_7', k1_tops_1('#skF_5', A_732)) | ~r1_tarski(A_732, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_111, c_50, c_5112])).
% 7.98/2.64  tff(c_5152, plain, (![A_732]: (m1_connsp_2(A_732, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', k1_tops_1('#skF_5', A_732)) | ~r1_tarski(A_732, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_5151])).
% 7.98/2.64  tff(c_5963, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4')) | ~r1_tarski('#skF_7', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_5946, c_5152])).
% 7.98/2.64  tff(c_6063, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1566, c_1924, c_12, c_42, c_5963])).
% 7.98/2.64  tff(c_6065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1105, c_6063])).
% 7.98/2.64  tff(c_6067, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 7.98/2.64  tff(c_6843, plain, (![E_1058, G_1059, C_1056, D_1057, B_1060, A_1055]: (r1_tmap_1(D_1057, B_1060, k3_tmap_1(A_1055, B_1060, C_1056, D_1057, E_1058), G_1059) | ~r1_tmap_1(C_1056, B_1060, E_1058, G_1059) | ~m1_pre_topc(D_1057, C_1056) | ~m1_subset_1(G_1059, u1_struct_0(D_1057)) | ~m1_subset_1(G_1059, u1_struct_0(C_1056)) | ~m1_subset_1(E_1058, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1056), u1_struct_0(B_1060)))) | ~v1_funct_2(E_1058, u1_struct_0(C_1056), u1_struct_0(B_1060)) | ~v1_funct_1(E_1058) | ~m1_pre_topc(D_1057, A_1055) | v2_struct_0(D_1057) | ~m1_pre_topc(C_1056, A_1055) | v2_struct_0(C_1056) | ~l1_pre_topc(B_1060) | ~v2_pre_topc(B_1060) | v2_struct_0(B_1060) | ~l1_pre_topc(A_1055) | ~v2_pre_topc(A_1055) | v2_struct_0(A_1055))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.98/2.64  tff(c_6845, plain, (![D_1057, A_1055, G_1059]: (r1_tmap_1(D_1057, '#skF_2', k3_tmap_1(A_1055, '#skF_2', '#skF_5', D_1057, '#skF_6'), G_1059) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_1059) | ~m1_pre_topc(D_1057, '#skF_5') | ~m1_subset_1(G_1059, u1_struct_0(D_1057)) | ~m1_subset_1(G_1059, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_1057, A_1055) | v2_struct_0(D_1057) | ~m1_pre_topc('#skF_5', A_1055) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1055) | ~v2_pre_topc(A_1055) | v2_struct_0(A_1055))), inference(resolution, [status(thm)], [c_56, c_6843])).
% 7.98/2.64  tff(c_6851, plain, (![D_1057, A_1055, G_1059]: (r1_tmap_1(D_1057, '#skF_2', k3_tmap_1(A_1055, '#skF_2', '#skF_5', D_1057, '#skF_6'), G_1059) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_1059) | ~m1_pre_topc(D_1057, '#skF_5') | ~m1_subset_1(G_1059, u1_struct_0(D_1057)) | ~m1_subset_1(G_1059, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1057, A_1055) | v2_struct_0(D_1057) | ~m1_pre_topc('#skF_5', A_1055) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1055) | ~v2_pre_topc(A_1055) | v2_struct_0(A_1055))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_60, c_58, c_6845])).
% 7.98/2.64  tff(c_7904, plain, (![D_1112, A_1113, G_1114]: (r1_tmap_1(D_1112, '#skF_2', k3_tmap_1(A_1113, '#skF_2', '#skF_5', D_1112, '#skF_6'), G_1114) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_1114) | ~m1_pre_topc(D_1112, '#skF_5') | ~m1_subset_1(G_1114, u1_struct_0(D_1112)) | ~m1_subset_1(G_1114, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1112, A_1113) | v2_struct_0(D_1112) | ~m1_pre_topc('#skF_5', A_1113) | ~l1_pre_topc(A_1113) | ~v2_pre_topc(A_1113) | v2_struct_0(A_1113))), inference(negUnitSimplification, [status(thm)], [c_80, c_64, c_6851])).
% 7.98/2.64  tff(c_6066, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 7.98/2.64  tff(c_7909, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_7904, c_6066])).
% 7.98/2.64  tff(c_7916, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_62, c_66, c_50, c_91, c_54, c_6067, c_7909])).
% 7.98/2.64  tff(c_7918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_7916])).
% 7.98/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.98/2.64  
% 7.98/2.64  Inference rules
% 7.98/2.64  ----------------------
% 7.98/2.64  #Ref     : 0
% 7.98/2.64  #Sup     : 1584
% 7.98/2.64  #Fact    : 0
% 7.98/2.64  #Define  : 0
% 7.98/2.64  #Split   : 39
% 7.98/2.64  #Chain   : 0
% 7.98/2.64  #Close   : 0
% 7.98/2.64  
% 7.98/2.64  Ordering : KBO
% 7.98/2.64  
% 7.98/2.64  Simplification rules
% 7.98/2.64  ----------------------
% 7.98/2.64  #Subsume      : 741
% 7.98/2.64  #Demod        : 972
% 7.98/2.64  #Tautology    : 188
% 7.98/2.64  #SimpNegUnit  : 64
% 7.98/2.64  #BackRed      : 0
% 7.98/2.64  
% 7.98/2.64  #Partial instantiations: 0
% 7.98/2.64  #Strategies tried      : 1
% 7.98/2.64  
% 7.98/2.64  Timing (in seconds)
% 7.98/2.64  ----------------------
% 7.98/2.64  Preprocessing        : 0.41
% 7.98/2.64  Parsing              : 0.21
% 7.98/2.64  CNF conversion       : 0.07
% 7.98/2.64  Main loop            : 1.45
% 7.98/2.64  Inferencing          : 0.45
% 7.98/2.64  Reduction            : 0.49
% 7.98/2.64  Demodulation         : 0.34
% 7.98/2.64  BG Simplification    : 0.04
% 7.98/2.64  Subsumption          : 0.37
% 7.98/2.64  Abstraction          : 0.05
% 7.98/2.64  MUC search           : 0.00
% 7.98/2.64  Cooper               : 0.00
% 7.98/2.64  Total                : 1.91
% 7.98/2.64  Index Insertion      : 0.00
% 7.98/2.64  Index Deletion       : 0.00
% 7.98/2.64  Index Matching       : 0.00
% 7.98/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
