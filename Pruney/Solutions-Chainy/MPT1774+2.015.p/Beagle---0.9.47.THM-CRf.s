%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:26 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 243 expanded)
%              Number of leaves         :   35 ( 110 expanded)
%              Depth                    :   12
%              Number of atoms          :  355 (1930 expanded)
%              Number of equality atoms :    6 (  76 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_259,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

tff(f_201,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ( ( v3_pre_topc(C,A)
                          & r1_tarski(C,u1_struct_0(B))
                          & r1_tarski(D,C)
                          & D = E )
                       => ( v3_pre_topc(E,B)
                        <=> v3_pre_topc(D,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tsep_1)).

tff(f_116,axiom,(
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

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_34,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_42,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_85,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_36,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_379,plain,(
    ! [B_729,C_730,A_731] :
      ( r1_tarski(u1_struct_0(B_729),u1_struct_0(C_730))
      | ~ m1_pre_topc(B_729,C_730)
      | ~ m1_pre_topc(C_730,A_731)
      | ~ m1_pre_topc(B_729,A_731)
      | ~ l1_pre_topc(A_731)
      | ~ v2_pre_topc(A_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_391,plain,(
    ! [B_729] :
      ( r1_tarski(u1_struct_0(B_729),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_729,'#skF_5')
      | ~ m1_pre_topc(B_729,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_379])).

tff(c_401,plain,(
    ! [B_729] :
      ( r1_tarski(u1_struct_0(B_729),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_729,'#skF_5')
      | ~ m1_pre_topc(B_729,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_391])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [C_695,B_696,A_697] :
      ( r2_hidden(C_695,B_696)
      | ~ r2_hidden(C_695,A_697)
      | ~ r1_tarski(A_697,B_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_208,plain,(
    ! [A_709,B_710,B_711] :
      ( r2_hidden('#skF_1'(A_709,B_710),B_711)
      | ~ r1_tarski(A_709,B_711)
      | r1_tarski(A_709,B_710) ) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_219,plain,(
    ! [A_712,B_713,B_714,B_715] :
      ( r2_hidden('#skF_1'(A_712,B_713),B_714)
      | ~ r1_tarski(B_715,B_714)
      | ~ r1_tarski(A_712,B_715)
      | r1_tarski(A_712,B_713) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_322,plain,(
    ! [A_725,B_726] :
      ( r2_hidden('#skF_1'(A_725,B_726),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_725,'#skF_7')
      | r1_tarski(A_725,B_726) ) ),
    inference(resolution,[status(thm)],[c_36,c_219])).

tff(c_793,plain,(
    ! [A_762,B_763,B_764] :
      ( r2_hidden('#skF_1'(A_762,B_763),B_764)
      | ~ r1_tarski(u1_struct_0('#skF_4'),B_764)
      | ~ r1_tarski(A_762,'#skF_7')
      | r1_tarski(A_762,B_763) ) ),
    inference(resolution,[status(thm)],[c_322,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_802,plain,(
    ! [B_765,A_766] :
      ( ~ r1_tarski(u1_struct_0('#skF_4'),B_765)
      | ~ r1_tarski(A_766,'#skF_7')
      | r1_tarski(A_766,B_765) ) ),
    inference(resolution,[status(thm)],[c_793,c_4])).

tff(c_808,plain,(
    ! [A_766] :
      ( ~ r1_tarski(A_766,'#skF_7')
      | r1_tarski(A_766,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_401,c_802])).

tff(c_824,plain,(
    ! [A_766] :
      ( ~ r1_tarski(A_766,'#skF_7')
      | r1_tarski(A_766,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48,c_808])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_84,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_76])).

tff(c_207,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_82])).

tff(c_217,plain,(
    r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_83])).

tff(c_961,plain,(
    ! [H_777,D_774,A_778,E_775,B_776,C_772,F_773] :
      ( r1_tmap_1(D_774,B_776,E_775,H_777)
      | ~ r1_tmap_1(C_772,B_776,k3_tmap_1(A_778,B_776,D_774,C_772,E_775),H_777)
      | ~ r1_tarski(F_773,u1_struct_0(C_772))
      | ~ r2_hidden(H_777,F_773)
      | ~ v3_pre_topc(F_773,D_774)
      | ~ m1_subset_1(H_777,u1_struct_0(C_772))
      | ~ m1_subset_1(H_777,u1_struct_0(D_774))
      | ~ m1_subset_1(F_773,k1_zfmisc_1(u1_struct_0(D_774)))
      | ~ m1_pre_topc(C_772,D_774)
      | ~ m1_subset_1(E_775,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_774),u1_struct_0(B_776))))
      | ~ v1_funct_2(E_775,u1_struct_0(D_774),u1_struct_0(B_776))
      | ~ v1_funct_1(E_775)
      | ~ m1_pre_topc(D_774,A_778)
      | v2_struct_0(D_774)
      | ~ m1_pre_topc(C_772,A_778)
      | v2_struct_0(C_772)
      | ~ l1_pre_topc(B_776)
      | ~ v2_pre_topc(B_776)
      | v2_struct_0(B_776)
      | ~ l1_pre_topc(A_778)
      | ~ v2_pre_topc(A_778)
      | v2_struct_0(A_778) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_965,plain,(
    ! [F_773] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ r1_tarski(F_773,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_773)
      | ~ v3_pre_topc(F_773,'#skF_5')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_773,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_217,c_961])).

tff(c_972,plain,(
    ! [F_773] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ r1_tarski(F_773,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_773)
      | ~ v3_pre_topc(F_773,'#skF_5')
      | ~ m1_subset_1(F_773,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_72,c_70,c_60,c_56,c_54,c_52,c_50,c_48,c_44,c_85,c_965])).

tff(c_1003,plain,(
    ! [F_781] :
      ( ~ r1_tarski(F_781,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_781)
      | ~ v3_pre_topc(F_781,'#skF_5')
      | ~ m1_subset_1(F_781,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_74,c_62,c_58,c_207,c_972])).

tff(c_1009,plain,(
    ! [A_782] :
      ( ~ r1_tarski(A_782,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_782)
      | ~ v3_pre_topc(A_782,'#skF_5')
      | ~ r1_tarski(A_782,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16,c_1003])).

tff(c_1052,plain,(
    ! [A_785] :
      ( ~ r1_tarski(A_785,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_785)
      | ~ v3_pre_topc(A_785,'#skF_5')
      | ~ r1_tarski(A_785,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_824,c_1009])).

tff(c_1061,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_1052])).

tff(c_1070,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38,c_1061])).

tff(c_40,plain,(
    v3_pre_topc('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_612,plain,(
    ! [E_742,B_743,A_744,C_745] :
      ( v3_pre_topc(E_742,B_743)
      | ~ v3_pre_topc(E_742,A_744)
      | ~ r1_tarski(E_742,C_745)
      | ~ r1_tarski(C_745,u1_struct_0(B_743))
      | ~ v3_pre_topc(C_745,A_744)
      | ~ m1_subset_1(E_742,k1_zfmisc_1(u1_struct_0(B_743)))
      | ~ m1_subset_1(E_742,k1_zfmisc_1(u1_struct_0(A_744)))
      | ~ m1_subset_1(C_745,k1_zfmisc_1(u1_struct_0(A_744)))
      | ~ m1_pre_topc(B_743,A_744)
      | ~ l1_pre_topc(A_744)
      | ~ v2_pre_topc(A_744) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1075,plain,(
    ! [B_787,B_788,A_789] :
      ( v3_pre_topc(B_787,B_788)
      | ~ r1_tarski(B_787,u1_struct_0(B_788))
      | ~ v3_pre_topc(B_787,A_789)
      | ~ m1_subset_1(B_787,k1_zfmisc_1(u1_struct_0(B_788)))
      | ~ m1_subset_1(B_787,k1_zfmisc_1(u1_struct_0(A_789)))
      | ~ m1_pre_topc(B_788,A_789)
      | ~ l1_pre_topc(A_789)
      | ~ v2_pre_topc(A_789) ) ),
    inference(resolution,[status(thm)],[c_12,c_612])).

tff(c_1426,plain,(
    ! [A_833,B_834,A_835] :
      ( v3_pre_topc(A_833,B_834)
      | ~ v3_pre_topc(A_833,A_835)
      | ~ m1_subset_1(A_833,k1_zfmisc_1(u1_struct_0(A_835)))
      | ~ m1_pre_topc(B_834,A_835)
      | ~ l1_pre_topc(A_835)
      | ~ v2_pre_topc(A_835)
      | ~ r1_tarski(A_833,u1_struct_0(B_834)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1075])).

tff(c_1433,plain,(
    ! [B_834] :
      ( v3_pre_topc('#skF_7',B_834)
      | ~ v3_pre_topc('#skF_7','#skF_3')
      | ~ m1_pre_topc(B_834,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_834)) ) ),
    inference(resolution,[status(thm)],[c_46,c_1426])).

tff(c_1441,plain,(
    ! [B_836] :
      ( v3_pre_topc('#skF_7',B_836)
      | ~ m1_pre_topc(B_836,'#skF_3')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_836)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_40,c_1433])).

tff(c_1445,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_824,c_1441])).

tff(c_1462,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_56,c_1445])).

tff(c_1464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1070,c_1462])).

tff(c_1466,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2011,plain,(
    ! [C_880,G_882,D_885,E_884,A_881,B_883] :
      ( r1_tmap_1(D_885,B_883,k3_tmap_1(A_881,B_883,C_880,D_885,E_884),G_882)
      | ~ r1_tmap_1(C_880,B_883,E_884,G_882)
      | ~ m1_pre_topc(D_885,C_880)
      | ~ m1_subset_1(G_882,u1_struct_0(D_885))
      | ~ m1_subset_1(G_882,u1_struct_0(C_880))
      | ~ m1_subset_1(E_884,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_880),u1_struct_0(B_883))))
      | ~ v1_funct_2(E_884,u1_struct_0(C_880),u1_struct_0(B_883))
      | ~ v1_funct_1(E_884)
      | ~ m1_pre_topc(D_885,A_881)
      | v2_struct_0(D_885)
      | ~ m1_pre_topc(C_880,A_881)
      | v2_struct_0(C_880)
      | ~ l1_pre_topc(B_883)
      | ~ v2_pre_topc(B_883)
      | v2_struct_0(B_883)
      | ~ l1_pre_topc(A_881)
      | ~ v2_pre_topc(A_881)
      | v2_struct_0(A_881) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2013,plain,(
    ! [D_885,A_881,G_882] :
      ( r1_tmap_1(D_885,'#skF_2',k3_tmap_1(A_881,'#skF_2','#skF_5',D_885,'#skF_6'),G_882)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_882)
      | ~ m1_pre_topc(D_885,'#skF_5')
      | ~ m1_subset_1(G_882,u1_struct_0(D_885))
      | ~ m1_subset_1(G_882,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_885,A_881)
      | v2_struct_0(D_885)
      | ~ m1_pre_topc('#skF_5',A_881)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_881)
      | ~ v2_pre_topc(A_881)
      | v2_struct_0(A_881) ) ),
    inference(resolution,[status(thm)],[c_50,c_2011])).

tff(c_2019,plain,(
    ! [D_885,A_881,G_882] :
      ( r1_tmap_1(D_885,'#skF_2',k3_tmap_1(A_881,'#skF_2','#skF_5',D_885,'#skF_6'),G_882)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_882)
      | ~ m1_pre_topc(D_885,'#skF_5')
      | ~ m1_subset_1(G_882,u1_struct_0(D_885))
      | ~ m1_subset_1(G_882,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_885,A_881)
      | v2_struct_0(D_885)
      | ~ m1_pre_topc('#skF_5',A_881)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_881)
      | ~ v2_pre_topc(A_881)
      | v2_struct_0(A_881) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_54,c_52,c_2013])).

tff(c_2023,plain,(
    ! [D_886,A_887,G_888] :
      ( r1_tmap_1(D_886,'#skF_2',k3_tmap_1(A_887,'#skF_2','#skF_5',D_886,'#skF_6'),G_888)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_888)
      | ~ m1_pre_topc(D_886,'#skF_5')
      | ~ m1_subset_1(G_888,u1_struct_0(D_886))
      | ~ m1_subset_1(G_888,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_886,A_887)
      | v2_struct_0(D_886)
      | ~ m1_pre_topc('#skF_5',A_887)
      | ~ l1_pre_topc(A_887)
      | ~ v2_pre_topc(A_887)
      | v2_struct_0(A_887) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_58,c_2019])).

tff(c_1465,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2026,plain,
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
    inference(resolution,[status(thm)],[c_2023,c_1465])).

tff(c_2029,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_60,c_44,c_85,c_48,c_1466,c_2026])).

tff(c_2031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:04:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.90  
% 4.90/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.90  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 4.90/1.90  
% 4.90/1.90  %Foreground sorts:
% 4.90/1.90  
% 4.90/1.90  
% 4.90/1.90  %Background operators:
% 4.90/1.90  
% 4.90/1.90  
% 4.90/1.90  %Foreground operators:
% 4.90/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.90/1.90  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.90/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.90/1.90  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.90/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.90/1.90  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.90/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.90/1.90  tff('#skF_7', type, '#skF_7': $i).
% 4.90/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.90/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.90/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.90/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.90/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.90/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.90/1.90  tff('#skF_9', type, '#skF_9': $i).
% 4.90/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.90/1.90  tff('#skF_8', type, '#skF_8': $i).
% 4.90/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.90/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.90/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/1.90  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.90/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.90/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.90/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.90/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.90/1.90  
% 4.90/1.92  tff(f_259, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 4.90/1.92  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.90/1.92  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.90/1.92  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.90/1.92  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.90/1.92  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.90/1.92  tff(f_201, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => ((((v3_pre_topc(C, A) & r1_tarski(C, u1_struct_0(B))) & r1_tarski(D, C)) & (D = E)) => (v3_pre_topc(E, B) <=> v3_pre_topc(D, A))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tsep_1)).
% 4.90/1.92  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.90/1.92  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_34, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_42, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_85, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 4.90/1.92  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.90/1.92  tff(c_38, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_36, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_379, plain, (![B_729, C_730, A_731]: (r1_tarski(u1_struct_0(B_729), u1_struct_0(C_730)) | ~m1_pre_topc(B_729, C_730) | ~m1_pre_topc(C_730, A_731) | ~m1_pre_topc(B_729, A_731) | ~l1_pre_topc(A_731) | ~v2_pre_topc(A_731))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.90/1.92  tff(c_391, plain, (![B_729]: (r1_tarski(u1_struct_0(B_729), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_729, '#skF_5') | ~m1_pre_topc(B_729, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_379])).
% 4.90/1.92  tff(c_401, plain, (![B_729]: (r1_tarski(u1_struct_0(B_729), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_729, '#skF_5') | ~m1_pre_topc(B_729, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_391])).
% 4.90/1.92  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.90/1.92  tff(c_132, plain, (![C_695, B_696, A_697]: (r2_hidden(C_695, B_696) | ~r2_hidden(C_695, A_697) | ~r1_tarski(A_697, B_696))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.90/1.92  tff(c_208, plain, (![A_709, B_710, B_711]: (r2_hidden('#skF_1'(A_709, B_710), B_711) | ~r1_tarski(A_709, B_711) | r1_tarski(A_709, B_710))), inference(resolution, [status(thm)], [c_6, c_132])).
% 4.90/1.92  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.90/1.92  tff(c_219, plain, (![A_712, B_713, B_714, B_715]: (r2_hidden('#skF_1'(A_712, B_713), B_714) | ~r1_tarski(B_715, B_714) | ~r1_tarski(A_712, B_715) | r1_tarski(A_712, B_713))), inference(resolution, [status(thm)], [c_208, c_2])).
% 4.90/1.92  tff(c_322, plain, (![A_725, B_726]: (r2_hidden('#skF_1'(A_725, B_726), u1_struct_0('#skF_4')) | ~r1_tarski(A_725, '#skF_7') | r1_tarski(A_725, B_726))), inference(resolution, [status(thm)], [c_36, c_219])).
% 4.90/1.92  tff(c_793, plain, (![A_762, B_763, B_764]: (r2_hidden('#skF_1'(A_762, B_763), B_764) | ~r1_tarski(u1_struct_0('#skF_4'), B_764) | ~r1_tarski(A_762, '#skF_7') | r1_tarski(A_762, B_763))), inference(resolution, [status(thm)], [c_322, c_2])).
% 4.90/1.92  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.90/1.92  tff(c_802, plain, (![B_765, A_766]: (~r1_tarski(u1_struct_0('#skF_4'), B_765) | ~r1_tarski(A_766, '#skF_7') | r1_tarski(A_766, B_765))), inference(resolution, [status(thm)], [c_793, c_4])).
% 4.90/1.92  tff(c_808, plain, (![A_766]: (~r1_tarski(A_766, '#skF_7') | r1_tarski(A_766, u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_401, c_802])).
% 4.90/1.92  tff(c_824, plain, (![A_766]: (~r1_tarski(A_766, '#skF_7') | r1_tarski(A_766, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48, c_808])).
% 4.90/1.92  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.90/1.92  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_76, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_84, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_76])).
% 4.90/1.92  tff(c_207, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_84])).
% 4.90/1.92  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_82, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_83, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_82])).
% 4.90/1.92  tff(c_217, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_207, c_83])).
% 4.90/1.92  tff(c_961, plain, (![H_777, D_774, A_778, E_775, B_776, C_772, F_773]: (r1_tmap_1(D_774, B_776, E_775, H_777) | ~r1_tmap_1(C_772, B_776, k3_tmap_1(A_778, B_776, D_774, C_772, E_775), H_777) | ~r1_tarski(F_773, u1_struct_0(C_772)) | ~r2_hidden(H_777, F_773) | ~v3_pre_topc(F_773, D_774) | ~m1_subset_1(H_777, u1_struct_0(C_772)) | ~m1_subset_1(H_777, u1_struct_0(D_774)) | ~m1_subset_1(F_773, k1_zfmisc_1(u1_struct_0(D_774))) | ~m1_pre_topc(C_772, D_774) | ~m1_subset_1(E_775, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_774), u1_struct_0(B_776)))) | ~v1_funct_2(E_775, u1_struct_0(D_774), u1_struct_0(B_776)) | ~v1_funct_1(E_775) | ~m1_pre_topc(D_774, A_778) | v2_struct_0(D_774) | ~m1_pre_topc(C_772, A_778) | v2_struct_0(C_772) | ~l1_pre_topc(B_776) | ~v2_pre_topc(B_776) | v2_struct_0(B_776) | ~l1_pre_topc(A_778) | ~v2_pre_topc(A_778) | v2_struct_0(A_778))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.90/1.92  tff(c_965, plain, (![F_773]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~r1_tarski(F_773, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_773) | ~v3_pre_topc(F_773, '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_773, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_217, c_961])).
% 4.90/1.92  tff(c_972, plain, (![F_773]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~r1_tarski(F_773, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_773) | ~v3_pre_topc(F_773, '#skF_5') | ~m1_subset_1(F_773, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_72, c_70, c_60, c_56, c_54, c_52, c_50, c_48, c_44, c_85, c_965])).
% 4.90/1.92  tff(c_1003, plain, (![F_781]: (~r1_tarski(F_781, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_781) | ~v3_pre_topc(F_781, '#skF_5') | ~m1_subset_1(F_781, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_74, c_62, c_58, c_207, c_972])).
% 4.90/1.92  tff(c_1009, plain, (![A_782]: (~r1_tarski(A_782, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_782) | ~v3_pre_topc(A_782, '#skF_5') | ~r1_tarski(A_782, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_16, c_1003])).
% 4.90/1.92  tff(c_1052, plain, (![A_785]: (~r1_tarski(A_785, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_785) | ~v3_pre_topc(A_785, '#skF_5') | ~r1_tarski(A_785, '#skF_7'))), inference(resolution, [status(thm)], [c_824, c_1009])).
% 4.90/1.92  tff(c_1061, plain, (~r2_hidden('#skF_8', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_36, c_1052])).
% 4.90/1.92  tff(c_1070, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38, c_1061])).
% 4.90/1.92  tff(c_40, plain, (v3_pre_topc('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.90/1.92  tff(c_612, plain, (![E_742, B_743, A_744, C_745]: (v3_pre_topc(E_742, B_743) | ~v3_pre_topc(E_742, A_744) | ~r1_tarski(E_742, C_745) | ~r1_tarski(C_745, u1_struct_0(B_743)) | ~v3_pre_topc(C_745, A_744) | ~m1_subset_1(E_742, k1_zfmisc_1(u1_struct_0(B_743))) | ~m1_subset_1(E_742, k1_zfmisc_1(u1_struct_0(A_744))) | ~m1_subset_1(C_745, k1_zfmisc_1(u1_struct_0(A_744))) | ~m1_pre_topc(B_743, A_744) | ~l1_pre_topc(A_744) | ~v2_pre_topc(A_744))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.90/1.92  tff(c_1075, plain, (![B_787, B_788, A_789]: (v3_pre_topc(B_787, B_788) | ~r1_tarski(B_787, u1_struct_0(B_788)) | ~v3_pre_topc(B_787, A_789) | ~m1_subset_1(B_787, k1_zfmisc_1(u1_struct_0(B_788))) | ~m1_subset_1(B_787, k1_zfmisc_1(u1_struct_0(A_789))) | ~m1_pre_topc(B_788, A_789) | ~l1_pre_topc(A_789) | ~v2_pre_topc(A_789))), inference(resolution, [status(thm)], [c_12, c_612])).
% 4.90/1.92  tff(c_1426, plain, (![A_833, B_834, A_835]: (v3_pre_topc(A_833, B_834) | ~v3_pre_topc(A_833, A_835) | ~m1_subset_1(A_833, k1_zfmisc_1(u1_struct_0(A_835))) | ~m1_pre_topc(B_834, A_835) | ~l1_pre_topc(A_835) | ~v2_pre_topc(A_835) | ~r1_tarski(A_833, u1_struct_0(B_834)))), inference(resolution, [status(thm)], [c_16, c_1075])).
% 4.90/1.92  tff(c_1433, plain, (![B_834]: (v3_pre_topc('#skF_7', B_834) | ~v3_pre_topc('#skF_7', '#skF_3') | ~m1_pre_topc(B_834, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski('#skF_7', u1_struct_0(B_834)))), inference(resolution, [status(thm)], [c_46, c_1426])).
% 4.90/1.92  tff(c_1441, plain, (![B_836]: (v3_pre_topc('#skF_7', B_836) | ~m1_pre_topc(B_836, '#skF_3') | ~r1_tarski('#skF_7', u1_struct_0(B_836)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_40, c_1433])).
% 4.90/1.92  tff(c_1445, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_824, c_1441])).
% 4.90/1.92  tff(c_1462, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_56, c_1445])).
% 4.90/1.92  tff(c_1464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1070, c_1462])).
% 4.90/1.92  tff(c_1466, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.90/1.92  tff(c_2011, plain, (![C_880, G_882, D_885, E_884, A_881, B_883]: (r1_tmap_1(D_885, B_883, k3_tmap_1(A_881, B_883, C_880, D_885, E_884), G_882) | ~r1_tmap_1(C_880, B_883, E_884, G_882) | ~m1_pre_topc(D_885, C_880) | ~m1_subset_1(G_882, u1_struct_0(D_885)) | ~m1_subset_1(G_882, u1_struct_0(C_880)) | ~m1_subset_1(E_884, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_880), u1_struct_0(B_883)))) | ~v1_funct_2(E_884, u1_struct_0(C_880), u1_struct_0(B_883)) | ~v1_funct_1(E_884) | ~m1_pre_topc(D_885, A_881) | v2_struct_0(D_885) | ~m1_pre_topc(C_880, A_881) | v2_struct_0(C_880) | ~l1_pre_topc(B_883) | ~v2_pre_topc(B_883) | v2_struct_0(B_883) | ~l1_pre_topc(A_881) | ~v2_pre_topc(A_881) | v2_struct_0(A_881))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.90/1.92  tff(c_2013, plain, (![D_885, A_881, G_882]: (r1_tmap_1(D_885, '#skF_2', k3_tmap_1(A_881, '#skF_2', '#skF_5', D_885, '#skF_6'), G_882) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_882) | ~m1_pre_topc(D_885, '#skF_5') | ~m1_subset_1(G_882, u1_struct_0(D_885)) | ~m1_subset_1(G_882, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_885, A_881) | v2_struct_0(D_885) | ~m1_pre_topc('#skF_5', A_881) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_881) | ~v2_pre_topc(A_881) | v2_struct_0(A_881))), inference(resolution, [status(thm)], [c_50, c_2011])).
% 4.90/1.92  tff(c_2019, plain, (![D_885, A_881, G_882]: (r1_tmap_1(D_885, '#skF_2', k3_tmap_1(A_881, '#skF_2', '#skF_5', D_885, '#skF_6'), G_882) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_882) | ~m1_pre_topc(D_885, '#skF_5') | ~m1_subset_1(G_882, u1_struct_0(D_885)) | ~m1_subset_1(G_882, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_885, A_881) | v2_struct_0(D_885) | ~m1_pre_topc('#skF_5', A_881) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_881) | ~v2_pre_topc(A_881) | v2_struct_0(A_881))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_54, c_52, c_2013])).
% 4.90/1.92  tff(c_2023, plain, (![D_886, A_887, G_888]: (r1_tmap_1(D_886, '#skF_2', k3_tmap_1(A_887, '#skF_2', '#skF_5', D_886, '#skF_6'), G_888) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_888) | ~m1_pre_topc(D_886, '#skF_5') | ~m1_subset_1(G_888, u1_struct_0(D_886)) | ~m1_subset_1(G_888, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_886, A_887) | v2_struct_0(D_886) | ~m1_pre_topc('#skF_5', A_887) | ~l1_pre_topc(A_887) | ~v2_pre_topc(A_887) | v2_struct_0(A_887))), inference(negUnitSimplification, [status(thm)], [c_74, c_58, c_2019])).
% 4.90/1.92  tff(c_1465, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.90/1.92  tff(c_2026, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2023, c_1465])).
% 4.90/1.92  tff(c_2029, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_60, c_44, c_85, c_48, c_1466, c_2026])).
% 4.90/1.92  tff(c_2031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2029])).
% 4.90/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.92  
% 4.90/1.92  Inference rules
% 4.90/1.92  ----------------------
% 4.90/1.92  #Ref     : 0
% 4.90/1.92  #Sup     : 414
% 4.90/1.92  #Fact    : 0
% 4.90/1.92  #Define  : 0
% 4.90/1.92  #Split   : 26
% 4.90/1.92  #Chain   : 0
% 4.90/1.92  #Close   : 0
% 4.90/1.92  
% 4.90/1.92  Ordering : KBO
% 4.90/1.92  
% 4.90/1.92  Simplification rules
% 4.90/1.92  ----------------------
% 4.90/1.92  #Subsume      : 157
% 4.90/1.92  #Demod        : 270
% 4.90/1.92  #Tautology    : 72
% 4.90/1.92  #SimpNegUnit  : 10
% 4.90/1.92  #BackRed      : 0
% 4.90/1.92  
% 4.90/1.92  #Partial instantiations: 0
% 4.90/1.92  #Strategies tried      : 1
% 4.90/1.92  
% 4.90/1.92  Timing (in seconds)
% 4.90/1.92  ----------------------
% 4.90/1.92  Preprocessing        : 0.41
% 4.90/1.92  Parsing              : 0.20
% 4.90/1.92  CNF conversion       : 0.08
% 4.90/1.92  Main loop            : 0.71
% 4.90/1.92  Inferencing          : 0.23
% 4.90/1.92  Reduction            : 0.23
% 4.90/1.92  Demodulation         : 0.16
% 4.90/1.92  BG Simplification    : 0.03
% 4.90/1.92  Subsumption          : 0.18
% 4.90/1.92  Abstraction          : 0.03
% 4.90/1.92  MUC search           : 0.00
% 4.90/1.92  Cooper               : 0.00
% 4.90/1.92  Total                : 1.16
% 4.90/1.92  Index Insertion      : 0.00
% 4.90/1.92  Index Deletion       : 0.00
% 4.90/1.92  Index Matching       : 0.00
% 4.90/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
